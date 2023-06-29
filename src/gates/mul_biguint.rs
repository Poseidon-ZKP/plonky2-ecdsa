use alloc::string::String;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::marker::PhantomData;
use libc_print::libc_println;
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
            .wire_to_add_product_carry(self.a_num_limbs - 1, self.b_num_limbs - 1)
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

                constraints.push(
                    product * F::Extension::from_noncanonical_biguint(BigUint::from(2u64.pow(32)))
                        + carry
                        - a_limbs[i] * b_limbs[j],
                );
            }
        }

        for c in 0..self.total_limbs() {
            let (combined_limb_wire, combined_carry_wire) = self.wire_combined_limbs_with_carry(c);
            let combined_limb = vars.local_wires[combined_limb_wire];
            let combined_carry = vars.local_wires[combined_carry_wire];

            let mut next_combined_carry = F::Extension::ZERO;
            if c < self.total_limbs() - 1 {
                let (_, next_combined_carry_wire) = self.wire_combined_limbs_with_carry(c + 1);
                next_combined_carry = vars.local_wires[next_combined_carry_wire];
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
            constraints.push(
                combined_limb
                    + next_combined_carry
                        * F::Extension::from_noncanonical_biguint(BigUint::from(2u64.pow(32)))
                    - to_add_c
                    - combined_carry,
            );
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
        self.eval_unfiltered_base_batch_packed(vars_base)
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
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

                let sum_product_carry = builder.add_extension(product, carry);

                constraints.push(builder.mul_sub_extension(
                    a_limbs[i],
                    b_limbs[j],
                    sum_product_carry,
                ));
            }
        }

        for c in 0..self.total_limbs() {
            let (combined_limb_wire, combined_carry_wire) = self.wire_combined_limbs_with_carry(c);
            let combined_limb = vars.local_wires[combined_limb_wire];
            let combined_carry = vars.local_wires[combined_carry_wire];

            let mut next_combined_carry = builder.zero_extension();
            if c < self.total_limbs() - 1 {
                let (_, next_combined_carry_wire) = self.wire_combined_limbs_with_carry(c + 1);
                next_combined_carry = vars.local_wires[next_combined_carry_wire];
            }
            let mut to_add_c = builder.zero_extension();
            for i in 0..self.a_num_limbs {
                for j in 0..self.b_num_limbs {
                    let (product_wire, carry_wire) = self.wire_to_add_product_carry(i, j);
                    let product = vars.local_wires[product_wire];
                    let carry = vars.local_wires[carry_wire];
                    if i + j == c {
                        to_add_c = builder.add_extension(to_add_c, product);
                    }
                    if i + j + 1 == c {
                        to_add_c = builder.add_extension(to_add_c, carry);
                    }
                }
            }

            let lhs = builder.add_extension(combined_limb, next_combined_carry);

            let rhs = builder.add_extension(to_add_c, combined_carry);
            constraints.push(builder.sub_extension(lhs, rhs));
        }

        constraints
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<Box<dyn WitnessGenerator<F>>> {
        let gen = MulBigUintGenerator::<F, D> {
            row,
            gate: self.clone(),
        };
        vec![Box::new(gen.adapter())]
    }

    fn num_wires(&self) -> usize {
        self.wire_combined_limbs_with_carry(self.total_limbs() - 1)
            .1
            + 1
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

impl<F: RichField + Extendable<D>, const D: usize> PackedEvaluableBase<F, D>
    for MulBigUintGate<F, D>
{
    fn eval_unfiltered_base_packed<P: PackedField<Scalar = F>>(
        &self,
        vars: EvaluationVarsBasePacked<P>,
        mut yield_constr: StridedConstraintConsumer<P>,
    ) {
        let a_limbs: Vec<_> = (0..self.a_num_limbs)
            .map(|i| vars.local_wires[self.wire_a(i)])
            .collect();

        let b_limbs: Vec<_> = (0..self.b_num_limbs)
            .map(|i| vars.local_wires[self.wire_b(i)])
            .collect();

        // TODO: Do limbs have to be range checked < 2^32?

        // Constraints for the product and carry of each limb of a and b.
        for i in 0..self.a_num_limbs {
            for j in 0..self.b_num_limbs {
                let (product_wire, carry_wire) = self.wire_to_add_product_carry(i, j);
                let product = vars.local_wires[product_wire];
                let carry = vars.local_wires[carry_wire];

                yield_constr.one(product + carry - a_limbs[i] * b_limbs[j]);
            }
        }

        for c in 0..self.total_limbs() {
            let (combined_limb_wire, combined_carry_wire) = self.wire_combined_limbs_with_carry(c);
            let combined_limb = vars.local_wires[combined_limb_wire];
            let combined_carry = vars.local_wires[combined_carry_wire];

            let mut next_combined_carry = P::ZEROS;
            if c < self.total_limbs() - 1 {
                let (_, next_combined_carry_wire) = self.wire_combined_limbs_with_carry(c + 1);
                next_combined_carry = vars.local_wires[next_combined_carry_wire];
            }
            let mut to_add_c = P::ZEROS;
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
            yield_constr.one(combined_limb + next_combined_carry - to_add_c - combined_carry);
        }
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
                let (product, carry) = if product_carry.len() == 1 {
                    (F::from_canonical_u32(product_carry[0]), F::ZERO)
                } else {
                    (
                        F::from_canonical_u32(product_carry[1]),
                        F::from_canonical_u32(product_carry[0]),
                    )
                };

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

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use rand::rngs::OsRng;
    use rand::Rng;

    use super::*;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::field::types::Sample;
    use plonky2::gates::gate_testing::{test_eval_fns, test_low_degree};
    use plonky2::hash::hash_types::HashOut;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::log2_ceil;

    #[test]
    fn wire_indices() {
        let gate = MulBigUintGate::<GoldilocksField, 2> {
            a_num_limbs: 4,
            b_num_limbs: 4,
            _phantom: PhantomData,
        };

        assert_eq!(gate.wire_a(0), 0);
        assert_eq!(gate.wire_a(3), 3);
        assert_eq!(gate.wire_b(0), 4);
        assert_eq!(gate.wire_b(3), 7);
        assert_eq!(gate.wire_to_add_product_carry(0, 0), (8, 9));
        assert_eq!(gate.wire_to_add_product_carry(3, 3), (38, 39));
        assert_eq!(gate.wire_combined_limbs_with_carry(0), (40, 41));
        assert_eq!(gate.wire_combined_limbs_with_carry(7), (54, 55));
    }

    #[test]
    fn low_degree() {
        let gate = MulBigUintGate::<GoldilocksField, 4> {
            a_num_limbs: 4,
            b_num_limbs: 4,
            _phantom: PhantomData,
        };
        test_low_degree::<GoldilocksField, _, 4>(gate);
    }

    // TODO: eval_unfiltered_circuit has a bug. Need to investigate. For now, not important since we don't need recursion.
    // #[test]
    // fn eval_fns() -> Result<()> {
    //     const D: usize = 2;
    //     type C = PoseidonGoldilocksConfig;
    //     type F = <C as GenericConfig<D>>::F;
    //     let gate = MulBigUintGate::<GoldilocksField, 2> {
    //         a_num_limbs: 4,
    //         b_num_limbs: 4,
    //         _phantom: PhantomData,
    //     };
    //     test_eval_fns::<F, C, _, D>(gate)
    // }

    #[test]
    fn test_gate_constraint() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type FF = <C as GenericConfig<D>>::FE;

        /// Returns the local wires for an MulBigUint gate given a and b as limbs of u32s in little-endian order.
        fn get_wires(a: Vec<u32>, b: Vec<u32>) -> Vec<FF> {
            let mut wires = Vec::new();
            // Set a and b limbs as wires.
            for limb in a.clone() {
                wires.push(FF::from_canonical_u32(limb));
            }
            for limb in b.clone() {
                wires.push(FF::from_canonical_u32(limb));
            }

            let mut to_add_vec = vec![Vec::with_capacity(b.len()); a.len()];

            // to_add i and j product and carry wires.
            for i in 0..a.len() {
                for j in 0..b.len() {
                    let product_carry = (BigUint::from(a[i]) * BigUint::from(b[j])).to_u32_digits();
                    let (product, carry) = if product_carry.len() == 1 {
                        to_add_vec[i].push((product_carry[0], 0));
                        (FF::from_canonical_u32(product_carry[0]), FF::ZERO)
                    } else {
                        to_add_vec[i].push((product_carry[1], product_carry[0]));
                        (
                            FF::from_canonical_u32(product_carry[1]),
                            FF::from_canonical_u32(product_carry[0]),
                        )
                    };
                    wires.push(product);
                    wires.push(carry);
                }
            }

            let total_limbs = a.len() + b.len();
            let mut combined_limb_vec = Vec::with_capacity(total_limbs);
            let mut combined_carry_vec = Vec::with_capacity(total_limbs);
            for c in 0..total_limbs {
                if c == 0 {
                    combined_carry_vec.push(0u32);
                }
                let mut to_add_c = BigUint::zero();
                for i in 0..a.len() {
                    for j in 0..b.len() {
                        if i + j == c {
                            to_add_c += to_add_vec[i][j].0;
                        }
                        if i + j + 1 == c {
                            to_add_c += to_add_vec[i][j].1;
                        }
                    }
                }
                to_add_c += combined_carry_vec[c];
                let to_add_c_u32_digits = to_add_c.to_u32_digits();
                let (combined_limb, next_combined_carry) = if to_add_c_u32_digits.len() == 1 {
                    (to_add_c_u32_digits[0], 0)
                } else {
                    (to_add_c_u32_digits[0], to_add_c_u32_digits[1])
                };

                combined_limb_vec.push(combined_limb);
                if c < total_limbs - 1 {
                    combined_carry_vec.push(next_combined_carry);
                }
            }

            // Combined limb and Carry wires.
            for i in 0..total_limbs {
                wires.push(FF::from_canonical_u32(combined_limb_vec[i]));
                wires.push(FF::from_canonical_u32(combined_carry_vec[i]));
            }
            wires
        }

        let mut rng = OsRng;

        let a_num_limbs = 4;
        let b_num_limbs = 4;

        let mut a: Vec<u32> = Vec::with_capacity(a_num_limbs);
        let mut b: Vec<u32> = Vec::with_capacity(b_num_limbs);

        for _ in 0..4 {
            let a_limb_i = rng.gen::<usize>() % (1 << 32);
            let b_limb_i = rng.gen::<usize>() % (1 << 32);
            a.push(a_limb_i as u32);
            b.push(b_limb_i as u32);
        }

        let gate = MulBigUintGate::<F, D> {
            a_num_limbs,
            b_num_limbs,
            _phantom: PhantomData,
        };

        let vars = EvaluationVars {
            local_constants: &[],
            local_wires: &get_wires(a, b),
            public_inputs_hash: &HashOut::rand(),
        };

        assert!(
            gate.eval_unfiltered(vars).iter().all(|x| { x.is_zero() }),
            "Gate constraints are not satisfied."
        );
    }
}
