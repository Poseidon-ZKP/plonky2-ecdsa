use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::marker::PhantomData;
use num::{BigUint, Zero};

use alloc::boxed::Box;
use plonky2::field::extension::Extendable;
use plonky2::field::ops::Square;
use plonky2::field::packed::PackedField;
use plonky2::field::types::Field;
use plonky2::gates::gate::Gate;
use plonky2::gates::packed_util::PackedEvaluableBase;
use plonky2::gates::util::StridedConstraintConsumer;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::generator::{GeneratedValues, SimpleGenerator, WitnessGenerator};
use plonky2::iop::target::Target;
use plonky2::iop::wire::Wire;
use plonky2::iop::witness::{PartitionWitness, Witness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::vars::{
    EvaluationTargets, EvaluationVars, EvaluationVarsBase, EvaluationVarsBaseBatch,
    EvaluationVarsBasePacked,
};
use plonky2::util::serialization::{Buffer, IoResult, Read, Write};

/// A gate for multiplying a * b, where a and b are big unsigned integers.
#[derive(Clone, Debug, Default)]
pub struct MulBigUintGate<F: RichField + Extendable<D>, const D: usize> {
    pub a_num_limbs: usize,
    pub b_num_limbs: usize,
    pub _phantom: PhantomData<F>,
}

// Mainly includes helper functions for computing wire indices.
impl<F: RichField + Extendable<D>, const D: usize> MulBigUintGate<F, D> {
    pub fn new(a_num_limbs: usize, b_num_limbs: usize) -> Self {
        Self {
            a_num_limbs,
            b_num_limbs,
            _phantom: PhantomData,
        }
    }

    pub fn total_limbs(&self) -> usize {
        self.a_num_limbs + self.b_num_limbs
    }

    /// The wire for the i-th limb of `a` input.
    /// a_num_limbs wires in [0 to a_num_limbs - 1].
    pub fn wire_a(&self, i: usize) -> usize {
        i
    }

    /// The wire for the i-th limb of `b` input.
    /// b_num_limbs wires in [a_num_limbs to a_num_limbs + b_num_limbs - 1].
    pub fn wire_b(&self, i: usize) -> usize {
        self.a_num_limbs + i
    }

    /// Wires indices for the product and carry from multiplying the i-th limb of `a` with the j-th limb of `b`.
    pub fn wire_to_add_product_carry(&self, i: usize, j: usize) -> (usize, usize) {
        let product_wire = self.total_limbs() + (i * self.b_num_limbs + j) * 2;
        let carry_wire = product_wire + 1;
        (product_wire, carry_wire)
    }

    // Wire indices for ith combined limb and carry
    pub fn wire_combined_limbs_with_carry(&self, i: usize) -> (usize, usize) {
        let first_empty_wire = self
            .wire_to_add_product_carry(self.a_num_limbs, self.b_num_limbs)
            .1
            + 1;
        let combined_limb_wire = first_empty_wire + i * 2;
        let combined_carry_wire = combined_limb_wire + 1;
        (combined_limb_wire, combined_carry_wire)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for MulBigUintGate<F, D> {
    fn id(&self) -> String {
        format!("{self:?}<D={D}>")
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let a_limbs: Vec<_> = (0..self.a_num_limbs)
            .map(|i| vars.local_wires[self.wire_a(i)])
            .collect();

        let b_limbs: Vec<_> = (0..self.b_num_limbs)
            .map(|i| vars.local_wires[self.wire_b(i)])
            .collect();

        // TODO: Do limbs have to be range checked < 2^32?

        let mut constraints = Vec::with_capacity(self.num_constraints());

        // Constraints for the product and carry of each limb of a and b.
        for i in 0..self.a_num_limbs {
            for j in 0..self.b_num_limbs {
                let (product_wire, carry_wire) = self.wire_to_add_product_carry(i, j);
                let product = vars.local_wires[product_wire];
                let carry = vars.local_wires[carry_wire];

                constraints.push(product + carry - a_limbs[i] * b_limbs[j]);
            }
        }

        for c in 0..self.total_limbs() {
            let (combined_limb_wire, combined_carry_wire) = self.wire_combined_limbs_with_carry(c);
            let combined_limb = vars.local_wires[combined_limb_wire];
            let combined_carry = vars.local_wires[combined_carry_wire];

            let next_combined_carry = F::Extension::ZERO;
            if c < self.total_limbs() - 1 {
                let (_, next_combined_carry_wire) = self.wire_combined_limbs_with_carry(c + 1);
                let next_combined_carry = vars.local_wires[next_combined_carry_wire];
            }
            let mut to_add_c = F::Extension::ZERO;
            for i in 0..self.a_num_limbs {
                for j in 0..self.b_num_limbs {
                    let (product_wire, carry_wire) = self.wire_to_add_product_carry(i, j);
                    let product = vars.local_wires[product_wire];
                    let carry = vars.local_wires[carry_wire];
                    if i + j == c {
                        to_add_c += product;
                    }
                    if i + j + 1 == c {
                        to_add_c += carry;
                    }
                }
            }
            constraints.push(combined_limb + next_combined_carry - to_add_c - combined_carry);
        }

        constraints
    }

    fn eval_unfiltered_base_one(
        &self,
        _vars: EvaluationVarsBase<F>,
        _yield_constr: StridedConstraintConsumer<F>,
    ) {
        panic!("use eval_unfiltered_base_packed instead");
    }

    fn eval_unfiltered_base_batch(&self, vars_base: EvaluationVarsBaseBatch<F>) -> Vec<F> {
        todo!("implement eval_unfiltered_base_batch")
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        todo!("Will implement if we need recursion")
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<Box<dyn WitnessGenerator<F>>> {
        let gen = MulBigUintGenerator::<F, D> {
            row,
            gate: self.clone(),
        };
        vec![Box::new(gen.adapter())]
    }

    fn num_wires(&self) -> usize {
        self.wire_combined_limbs_with_carry(self.total_limbs()).1 + 1
    }

    fn num_constants(&self) -> usize {
        0
    }

    fn degree(&self) -> usize {
        2
    }

    fn num_constraints(&self) -> usize {
        self.a_num_limbs * self.b_num_limbs + self.total_limbs()
    }
}

#[derive(Debug, Default)]
pub struct MulBigUintGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    gate: MulBigUintGate<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F>
    for MulBigUintGenerator<F, D>
{
    fn dependencies(&self) -> Vec<Target> {
        let local_target = |column| Target::wire(self.row, column);

        let mut deps = Vec::with_capacity(self.gate.a_num_limbs + self.gate.b_num_limbs);
        for i in 0..self.gate.a_num_limbs {
            deps.push(local_target(self.gate.wire_a(i)));
        }
        for i in 0..self.gate.b_num_limbs {
            deps.push(local_target(self.gate.wire_b(i)));
        }
        deps
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let local_wire = |column| Wire {
            row: self.row,
            column,
        };

        let get_local_wire = |column| witness.get_wire(local_wire(column));

        // Load in a and b
        // This is a bit inefficient, we could load in the limbs in parallel.
        let a_limbs: Vec<_> = (0..self.gate.a_num_limbs)
            .map(|i| get_local_wire(self.gate.wire_a(i)))
            .collect();

        let b_limbs: Vec<_> = (0..self.gate.b_num_limbs)
            .map(|i| get_local_wire(self.gate.wire_b(i)))
            .collect();

        for i in 0..self.gate.a_num_limbs {
            for j in 0..self.gate.b_num_limbs {
                // TODO: Multiply limbs and get product and carry.
                let a_i = a_limbs[i].to_canonical_biguint();
                let b_j = b_limbs[j].to_canonical_biguint();
                let product_carry = (a_i * b_j).to_u32_digits();
                let (product, carry) = (
                    F::from_canonical_u32(product_carry[0]),
                    F::from_canonical_u32(product_carry[1]),
                );

                let (product_wire, carry_wire) = self.gate.wire_to_add_product_carry(i, j);
                out_buffer.set_wire(local_wire(product_wire), product);
                out_buffer.set_wire(local_wire(carry_wire), carry);
            }
        }

        for c in 0..self.gate.total_limbs() {
            let (combined_limb_wire, combined_carry_wire) =
                self.gate.wire_combined_limbs_with_carry(c);
            if c == 0 {
                // Set carry to 0
                out_buffer.set_wire(local_wire(combined_carry_wire), F::ZERO);
            }
            let mut to_add_c = BigUint::zero();
            for i in 0..self.gate.a_num_limbs {
                for j in 0..self.gate.b_num_limbs {
                    let (product_wire, carry_wire) = self.gate.wire_to_add_product_carry(i, j);
                    if i + j == c {
                        to_add_c += get_local_wire(product_wire).to_canonical_biguint();
                    }
                    if i + j + 1 == c {
                        to_add_c += get_local_wire(carry_wire).to_canonical_biguint();
                    }
                }
            }
            to_add_c += get_local_wire(combined_carry_wire).to_canonical_biguint();
            let to_add_c_u32_digits = to_add_c.to_u32_digits();
            let (combined_limb, next_combined_carry) = (
                F::from_canonical_u32(to_add_c_u32_digits[0]),
                F::from_canonical_u32(to_add_c_u32_digits[1]),
            );
            out_buffer.set_wire(local_wire(combined_limb_wire), combined_limb);
            if c < self.gate.total_limbs() - 1 {
                let (_, next_combined_carry_wire) = self.gate.wire_combined_limbs_with_carry(c + 1);
                out_buffer.set_wire(local_wire(next_combined_carry_wire), next_combined_carry);
            }
        }
    }
}
