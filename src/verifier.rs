pub use crate::utils::{
    get_omegas, get_proof, get_pubSignals, Omegas, Proof, ProofWithPubSignal,
};
use crate::utils::VerificationKey;
use ark_bn254::{g1::Parameters, Bn254, Fq, FqParameters, Fr, FrParameters};
use ark_bn254::{g2, Fq2, Fq2Parameters, G2Affine};
use ark_ec::group::Group;
use ark_ec::short_weierstrass_jacobian::GroupAffine;
use ark_ec::*;
use ark_ec::*;
use ark_ff::{
    field_new, Field, Fp256, Fp256Parameters, Fp2ParamsWrapper, One, PrimeField, QuadExtField,
    UniformRand, Zero,
};
use ark_poly::{domain, Polynomial};
use core::num;
use num_bigint::*;
use std::ops::{Add, Mul, Neg, Sub};
use std::str::FromStr;
use std::vec;

use num_bigint::BigUint;
use tiny_keccak::{Hasher, Keccak};

use crate::utils::{get_verification_key, PartialVerifierState};
use num_bigint::*;

pub type G1Point = <Bn254 as PairingEngine>::G1Affine;
pub type G2Point = <Bn254 as PairingEngine>::G2Affine;

pub fn verify() {
    println!("Verifying....");
    let mut pvs: PartialVerifierState = PartialVerifierState::new();
    get_challenges(&mut pvs);
    verify_quotient_evaluation(&mut pvs);

    let verification_key: VerificationKey = get_verification_key();
    let proof: Proof = get_proof();
    let vk_gate_setup_0_affine = verification_key.gate_setup[0];
    let vk_gate_setup_1_affine = verification_key.gate_setup[1];
    let vk_gate_setup_2_affine = verification_key.gate_setup[2];
    let vk_gate_setup_3_affine = verification_key.gate_setup[3];
    let vk_gate_setup_4_affine = verification_key.gate_setup[4];
    let vk_gate_setup_5_affine = verification_key.gate_setup[5];
    let vk_gate_setup_6_affine = verification_key.gate_setup[6];
    let vk_gate_setup_7_affine = verification_key.gate_setup[7];
    let vk_gate_selectors_0_affine = verification_key.gate_selectors[0];
    let vk_gate_selectors_1_affine = verification_key.gate_selectors[1];
    let vk_permutation_0_affine = verification_key.permutation[0];
    let vk_permutation_1_affine = verification_key.permutation[1];
    let vk_permutation_2_affine = verification_key.permutation[2];
    let vk_permutation_3_affine = verification_key.permutation[3];
    let vk_lookp_table_0_affine = verification_key.lookup_table[0];
    let vk_lookp_table_1_affine = verification_key.lookup_table[1];
    let vk_lookp_table_2_affine = verification_key.lookup_table[2];
    let vk_lookp_table_3_affine = verification_key.lookup_table[3];
    let vk_lookup_selector_affine = verification_key.lookup_selector;
    let vk_lookup_table_type_affine = verification_key.lookup_table_type;

    let queries = prepare_queries(
        vk_gate_setup_0_affine,
        vk_gate_setup_1_affine,
        vk_gate_setup_2_affine,
        vk_gate_setup_3_affine,
        vk_gate_setup_4_affine,
        vk_gate_setup_5_affine,
        vk_gate_setup_6_affine,
        vk_gate_setup_7_affine,
        vk_gate_selectors_1_affine,
        vk_permutation_3_affine,
        vk_lookp_table_0_affine,
        vk_lookp_table_1_affine,
        vk_lookp_table_2_affine,
        vk_lookp_table_3_affine,
        pvs.clone(),
        proof.clone(),
    );

    let lookup_s_first_aggregated_commitment_coeff = queries.3;

    prepare_aggregated_commitment(
        queries,
        vk_gate_selectors_0_affine,
        vk_gate_selectors_1_affine,
        vk_permutation_0_affine,
        vk_permutation_1_affine,
        vk_permutation_2_affine,
        vk_lookup_selector_affine,
        vk_lookup_table_type_affine,
        queries.2,
        lookup_s_first_aggregated_commitment_coeff,
        queries.4,
        queries.5,
        pvs.clone(),
        proof.clone(),
    );
}

fn add_assign_lookup_linearisation_contribution_with_v(
    queries_at_z_1: GroupAffine<Parameters>,
    state_opening_0_z: Fr,
    state_opening_1_z: Fr,
    state_opening_2_z: Fr,
    proof: Proof,
    pvs: PartialVerifierState
) -> (Fr, Fr) {

    let state_power_of_alpha_6 = pvs.power_of_alpha_6;
    let state_power_of_alpha_7 = pvs.power_of_alpha_7;
    let state_power_of_alpha_8 = pvs.power_of_alpha_8;
    let state_l_n_minus_1_at_z = pvs.l_n_minus_one_at_z;
    let state_z_minus_last_omega = pvs.z_minus_last_omega;
    let state_v_slot = pvs.v;
    let proof_lookup_t_poly_opening_at_z_omega = proof.lookup_t_poly_opening_at_z_omega;
    let proof_lookup_t_poly_opening_at_z = proof.lookup_t_poly_opening_at_z;
    let state_beta_lookup = pvs.beta_lookup;
    let state_beta_gamma_plus_gamma = pvs.beta_gamma_plus_gamma;
    let state_eta = pvs.eta;
    let proof_looup_table_type_poly_opening_at_z = proof.lookup_table_type_poly_opening_at_z;
    let proof_lookup_selector_poly_opening_at_z = proof.lookup_selector_poly_opening_at_z;
    let state_gamma_lookup = pvs.gamma_lookup;
    let state_beta_plus_one = pvs.beta_plus_one;
    let proof_lookup_grand_product_opening_at_z_omega = proof.lookup_grand_product_opening_at_z_omega;
    // check is this assignment even correct ??
    let mut factor = proof_lookup_grand_product_opening_at_z_omega;
    factor = factor.mul(state_power_of_alpha_6);
    factor = factor.mul(state_z_minus_last_omega);
    factor = factor.mul(state_v_slot);

    // saving factor into
    let lookup_s_first_aggregated_commitment_coeff = factor;

    factor = proof_lookup_t_poly_opening_at_z_omega;
    factor = factor.mul(state_beta_lookup);
    factor = factor.add(proof_lookup_t_poly_opening_at_z);
    factor = factor.add(state_beta_gamma_plus_gamma);

    let mut freconstructed = state_opening_0_z;
    let eta = state_eta;
    let mut currenteta = eta;

    freconstructed = currenteta.mul(state_opening_1_z).add(freconstructed);
    currenteta = currenteta.mul(eta);
    freconstructed = currenteta.mul(state_opening_2_z).add(freconstructed);
    currenteta = currenteta.mul(eta);

    freconstructed = freconstructed.add(proof_looup_table_type_poly_opening_at_z.mul(currenteta));
    freconstructed = freconstructed.mul(proof_lookup_selector_poly_opening_at_z);
    freconstructed = freconstructed.add(state_gamma_lookup);

    factor = factor.mul(freconstructed);
    factor = factor.mul(state_beta_plus_one);
    factor = -factor;
    factor = factor.mul(state_power_of_alpha_6);
    factor = factor.mul(state_z_minus_last_omega);

    let state_l_0_at_z = Fr::from_str(
        "16998705531439461081194953598960002453935573094468931463486819379249964474322",
    )
    .unwrap();

    factor = factor.add(state_l_0_at_z.mul(state_power_of_alpha_7));
    factor = factor.add(state_l_n_minus_1_at_z.mul(state_power_of_alpha_8));

    factor = factor.mul(state_v_slot);

    println!("Factor: {:?}", factor.to_string());

    (lookup_s_first_aggregated_commitment_coeff, factor)
}

fn add_assign_permutation_linearisation_contribution_with_v(
    queries_at_z_1: GroupAffine<Parameters>,
    state_opening_0_z: Fr,
    state_opening_1_z: Fr,
    state_opening_2_z: Fr,
    state_opening_3_z: Fr,
    vk_permutation_3_affine: GroupAffine<Parameters>,
    proof: Proof,
    pvs: PartialVerifierState,
) -> (GroupAffine<Parameters>, Fr) {
    let state_power_of_alpha_4 = pvs.power_of_alpha_4;
    let state_power_of_alpha_5 = pvs.power_of_alpha_5;
    let state_z_slot = pvs.z;
    let state_beta = pvs.beta;
    let state_gamma = pvs.gamma;
    let state_v_slot = pvs.v;

    let proof_copy_permutation_grand_product_opening_at_z_omega = proof.copy_permutation_grand_product_opening_at_z_omega;
    let proof_copy_permutation_polys_0_opening_at_z = proof.copy_permutation_polys_0_opening_at_z;
    let proof_copy_permutation_polys_1_opening_at_z = proof.copy_permutation_polys_1_opening_at_z;
    let proof_copy_permutation_polys_2_opening_at_z = proof.copy_permutation_polys_2_opening_at_z;

    let non_residue_0 = Fr::from_str("5").unwrap();
    let non_residue_1 = Fr::from_str("7").unwrap();
    let non_residue_2 = Fr::from_str("10").unwrap();

    let mut factor = state_power_of_alpha_4;
    let zmulbeta = state_z_slot.mul(state_beta);

    let mut intermediate_value = state_opening_0_z.add(zmulbeta.add(state_gamma));
    factor = factor.mul(intermediate_value);

    intermediate_value = (zmulbeta.mul(non_residue_0))
        .add(state_gamma)
        .add(state_opening_1_z);
    factor = factor.mul(intermediate_value);

    intermediate_value = (zmulbeta.mul(non_residue_1))
        .add(state_gamma)
        .add(state_opening_2_z);
    factor = factor.mul(intermediate_value);

    intermediate_value = (zmulbeta.mul(non_residue_2))
        .add(state_gamma)
        .add(state_opening_3_z);
    factor = factor.mul(intermediate_value);

    println!("Factor: {:?}", factor.to_string());
    println!("intermediate_value: {:?}", intermediate_value.to_string());

    let state_l_0_at_z = pvs.l_0_at_z;
    println!("State L 0 at Z: {:?}", state_l_0_at_z.to_string());


    factor = factor.add(state_l_0_at_z.mul(state_power_of_alpha_5));
    factor = factor.mul(state_v_slot);
    let copy_permutation_first_aggregated_commitment_coeff = factor;

    factor = state_power_of_alpha_4.mul(state_beta);

    factor = factor.mul(proof_copy_permutation_grand_product_opening_at_z_omega);

    println!("Factor 2: {:?}", factor.to_string());

    intermediate_value = state_opening_0_z
        .add(state_gamma.add(proof_copy_permutation_polys_0_opening_at_z.mul(state_beta)));
    factor = factor.mul(intermediate_value);

    intermediate_value = state_opening_1_z
        .add(state_gamma.add(proof_copy_permutation_polys_1_opening_at_z.mul(state_beta)));
    factor = factor.mul(intermediate_value);

    intermediate_value = state_opening_2_z
        .add(state_gamma.add(proof_copy_permutation_polys_2_opening_at_z.mul(state_beta)));
    factor = factor.mul(intermediate_value);

    println!("factor 2: {:?}", factor.to_string());
    println!("intermediate_value 2: {:?}", intermediate_value.to_string());

    factor = factor.mul(state_v_slot);

    let temp_query_val = vk_permutation_3_affine.mul(factor).into_affine();
    println!("Temp Query Val: {:?}", temp_query_val.x.to_string());
    println!("Temp Query Val: {:?}", temp_query_val.y.to_string());

    (
        queries_at_z_1.add(-temp_query_val),
        copy_permutation_first_aggregated_commitment_coeff,
    )
}

fn add_assign_rescue_customgate_linearisation_contribution_with_v(
    queries_at_z_1: GroupAffine<Parameters>,
    state_opening_0_z: Fr,
    state_opening_1_z: Fr,
    state_opening_2_z: Fr,
    state_opening_3_z: Fr,
    vk_gate_selectors_1_affine: GroupAffine<Parameters>,
    proof: Proof,
    pvs: PartialVerifierState,
) -> GroupAffine<Parameters> {
    // challenges wire later
    let state_alpha_slot = pvs.alpha;
    let state_power_of_alpha_2 = pvs.power_of_alpha_2;
    let state_power_of_alpha_3 = pvs.power_of_alpha_3;
    let state_v_slot = pvs.v;

    let mut accumulator: Fr;
    let mut intermediate_value: Fr;

    accumulator = state_opening_0_z.square();
    accumulator = accumulator.sub(state_opening_1_z);
    accumulator = accumulator.mul(state_alpha_slot);

    intermediate_value = state_opening_1_z.square();
    intermediate_value = intermediate_value.sub(state_opening_2_z);
    intermediate_value = intermediate_value.mul(state_power_of_alpha_2);
    accumulator = accumulator.add(intermediate_value);

    intermediate_value = state_opening_2_z.mul(state_opening_0_z);
    intermediate_value = intermediate_value.sub(state_opening_3_z);
    intermediate_value = intermediate_value.mul(state_power_of_alpha_3);
    accumulator = accumulator.add(intermediate_value);

    accumulator = accumulator.mul(state_v_slot);

    vk_gate_selectors_1_affine
        .mul(accumulator)
        .into_affine()
        .add(queries_at_z_1)
}

fn main_gate_linearisation_contribution_with_v(
    vk_gate_setup_0_affine: GroupAffine<Parameters>,
    vk_gate_setup_1_affine: GroupAffine<Parameters>,
    vk_gate_setup_2_affine: GroupAffine<Parameters>,
    vk_gate_setup_3_affine: GroupAffine<Parameters>,
    vk_gate_setup_4_affine: GroupAffine<Parameters>,
    vk_gate_setup_5_affine: GroupAffine<Parameters>,
    vk_gate_setup_6_affine: GroupAffine<Parameters>,
    vk_gate_setup_7_affine: GroupAffine<Parameters>,
    state_opening_0_z: Fr,
    state_opening_1_z: Fr,
    state_opening_2_z: Fr,
    state_opening_3_z: Fr,
    proof: Proof,
    pvs: PartialVerifierState,
) -> GroupAffine<Parameters> {
    let mut queries_at_z_1 = vk_gate_setup_0_affine.mul(state_opening_0_z).into_affine();
    queries_at_z_1 =
        queries_at_z_1.add(vk_gate_setup_1_affine.mul(state_opening_1_z).into_affine());
    queries_at_z_1 =
        queries_at_z_1.add(vk_gate_setup_2_affine.mul(state_opening_2_z).into_affine());
    queries_at_z_1 =
        queries_at_z_1.add(vk_gate_setup_3_affine.mul(state_opening_3_z).into_affine());
    queries_at_z_1 = queries_at_z_1.add(
        vk_gate_setup_4_affine
            .mul(state_opening_0_z.mul(state_opening_1_z))
            .into_affine(),
    );
    queries_at_z_1 = queries_at_z_1.add(
        vk_gate_setup_5_affine
            .mul(state_opening_0_z.mul(state_opening_2_z))
            .into_affine(),
    );
    queries_at_z_1 = queries_at_z_1.add(vk_gate_setup_6_affine);

    // proof value
    let proof_state_polys_3_opening_at_z_omega_slot = proof.state_poly_3_opening_at_z_omega;
    
    // proof value
    let proof_gate_selectors_0_opening_at_z = proof.gate_selectors_0_opening_at_z;

    // challenge
    let state_v_slot = pvs.v;

    queries_at_z_1 = queries_at_z_1.add(
        vk_gate_setup_7_affine
            .mul(proof_state_polys_3_opening_at_z_omega_slot)
            .into_affine(),
    );

    println!("Queries at Z 1 x Slot: {:?}", queries_at_z_1.x.to_string());
    println!("Queries at Z 1 y Slot: {:?}", queries_at_z_1.y.to_string());

    let coeff = proof_gate_selectors_0_opening_at_z.mul(state_v_slot);
    queries_at_z_1 = queries_at_z_1.mul(coeff).into_affine();

    queries_at_z_1
}

fn prepare_queries(
    vk_gate_setup_0_affine: GroupAffine<Parameters>,
    vk_gate_setup_1_affine: GroupAffine<Parameters>,
    vk_gate_setup_2_affine: GroupAffine<Parameters>,
    vk_gate_setup_3_affine: GroupAffine<Parameters>,
    vk_gate_setup_4_affine: GroupAffine<Parameters>,
    vk_gate_setup_5_affine: GroupAffine<Parameters>,
    vk_gate_setup_6_affine: GroupAffine<Parameters>,
    vk_gate_setup_7_affine: GroupAffine<Parameters>,
    vk_gate_selectors_1_affine: GroupAffine<Parameters>,
    vk_permutation_3_affine: GroupAffine<Parameters>,
    vk_lookp_table_0_affine: GroupAffine<Parameters>,
    vk_lookp_table_1_affine: GroupAffine<Parameters>,
    vk_lookp_table_2_affine: GroupAffine<Parameters>,
    vk_lookp_table_3_affine: GroupAffine<Parameters>,
    pvs: PartialVerifierState,
    proof: Proof,
) -> (
    GroupAffine<Parameters>,
    GroupAffine<Parameters>,
    Fr,
    Fr,
    GroupAffine<Parameters>,
    Fr,
) {
    let z_domain_size = pvs.z_in_domain_size;

    let mut current_z = z_domain_size;
    // println!("kjgdfsfjkdghdf k {:?} ", proof.q)
    let proof_quotient_poly_parts_0_affine = proof.quotient_poly_parts_0;

    let proof_quotient_poly_parts_1_affine = proof.quotient_poly_parts_1;

    let proof_quotient_poly_parts_2_affine = proof.quotient_poly_parts_2;

    let proof_quotient_poly_parts_3_affine = proof.quotient_poly_parts_3;

    let mut queries_at_z_0 = proof_quotient_poly_parts_1_affine
        .mul(z_domain_size)
        .into_affine()
        .add(proof_quotient_poly_parts_0_affine);

    current_z = current_z.mul(z_domain_size);

    queries_at_z_0 = proof_quotient_poly_parts_2_affine
        .mul(current_z)
        .into_affine()
        .add(queries_at_z_0);

    println!("Queries at Z 0 x Slot: {:?}", queries_at_z_0.x.to_string());
    println!("Queries at Z 0 y Slot: {:?}", queries_at_z_0.y.to_string());

    current_z = current_z.mul(z_domain_size);

    queries_at_z_0 = proof_quotient_poly_parts_3_affine
        .mul(current_z)
        .into_affine()
        .add(queries_at_z_0);

    println!("Queries at Z 0 x Slot: {:?}", queries_at_z_0.x.to_string());
    println!("Queries at Z 0 y Slot: {:?}", queries_at_z_0.y.to_string());

    let state_opening_0_z = proof.state_poly_0_opening_at_z;

    let state_opening_1_z = proof.state_poly_1_opening_at_z;

    let state_opening_2_z = proof.state_poly_2_opening_at_z;

    let state_opening_3_z = proof.state_poly_3_opening_at_z;

    let mut queries_at_z_1 = main_gate_linearisation_contribution_with_v(
        vk_gate_setup_0_affine,
        vk_gate_setup_1_affine,
        vk_gate_setup_2_affine,
        vk_gate_setup_3_affine,
        vk_gate_setup_4_affine,
        vk_gate_setup_5_affine,
        vk_gate_setup_6_affine,
        vk_gate_setup_7_affine,
        state_opening_0_z,
        state_opening_1_z,
        state_opening_2_z,
        state_opening_3_z,
        proof.clone(),
        pvs.clone()
    );

    println!("Queries at Z 1 x Slot: {:?}", queries_at_z_1.x.to_string());
    println!("Queries at Z 1 y Slot: {:?}", queries_at_z_1.y.to_string());

    queries_at_z_1 = add_assign_rescue_customgate_linearisation_contribution_with_v(
        queries_at_z_1,
        state_opening_0_z,
        state_opening_1_z,
        state_opening_2_z,
        state_opening_3_z,
        vk_gate_selectors_1_affine,
        proof.clone(),
        pvs.clone()
    );

    println!(" Queries at Z 1 x Slot: {:?}", queries_at_z_1.x.to_string());
    println!(" Queries at Z 1 y Slot: {:?}", queries_at_z_1.y.to_string());
    // PROOF_QUOTIENT_POLY_PARTS_1_X_SLOT currentz QUERIES_AT_Z_0_X_SLOT
    // queries_at_z_1

    let resp = add_assign_permutation_linearisation_contribution_with_v(
        queries_at_z_1,
        state_opening_0_z,
        state_opening_1_z,
        state_opening_2_z,
        state_opening_3_z,
        vk_permutation_3_affine,
        proof.clone(),
        pvs.clone()
    );

    queries_at_z_1 = resp.0;
    let copy_permutation_first_aggregated_commitment_coeff = resp.1;

    println!("Queries at Z 1 x Slot: {:?}", queries_at_z_1.x.to_string());
    println!("Queries at Z 1 y Slot: {:?}", queries_at_z_1.y.to_string());

    // we are assigning few things here internally which would be required later on
    let (
        lookup_s_first_aggregated_commitment_coeff,
        lookup_grand_product_first_aggregated_commitment_coeff,
    ) = add_assign_lookup_linearisation_contribution_with_v(
        queries_at_z_1,
        state_opening_0_z,
        state_opening_1_z,
        state_opening_2_z,
        proof.clone(),
        pvs.clone()
    );

    let state_eta = pvs.eta;

    let eta = state_eta;
    let mut currenteta = eta;

    let mut queries_t_poly_aggregated = vk_lookp_table_0_affine;
    queries_t_poly_aggregated = vk_lookp_table_1_affine
        .mul(currenteta)
        .into_affine()
        .add(queries_t_poly_aggregated);

    currenteta = currenteta.mul(eta);
    queries_t_poly_aggregated = vk_lookp_table_2_affine
        .mul(currenteta)
        .into_affine()
        .add(queries_t_poly_aggregated);
    currenteta = currenteta.mul(eta);

    queries_t_poly_aggregated = vk_lookp_table_3_affine
        .mul(currenteta)
        .into_affine()
        .add(queries_t_poly_aggregated);

    println!(
        "Queries T Poly Aggregated x Slot: {:?}",
        queries_t_poly_aggregated.x.to_string()
    );
    println!(
        "Queries T Poly Aggregated y Slot: {:?}",
        queries_t_poly_aggregated.y.to_string()
    );

    (
        queries_at_z_0,
        queries_at_z_1,
        copy_permutation_first_aggregated_commitment_coeff,
        lookup_s_first_aggregated_commitment_coeff,
        queries_t_poly_aggregated,
        lookup_grand_product_first_aggregated_commitment_coeff,
    )
}

fn prepare_aggregated_commitment(
    queries: (
        GroupAffine<Parameters>,
        GroupAffine<Parameters>,
        Fr,
        Fr,
        GroupAffine<Parameters>,
        Fr,
    ),
    vk_gate_selectors_0_affine: GroupAffine<Parameters>,
    vk_gate_selectors_1_affine: GroupAffine<Parameters>,
    vk_permutation_0_affine: GroupAffine<Parameters>,
    vk_permutation_1_affine: GroupAffine<Parameters>,
    vk_permutation_2_affine: GroupAffine<Parameters>,
    vk_lookup_selector_affine: GroupAffine<Parameters>,
    vk_lookup_table_type_affine: GroupAffine<Parameters>,
    copy_permutation_first_aggregated_commitment_coeff: Fr,
    lookup_s_first_aggregated_commitment_coeff: Fr,
    queries_t_poly_aggregated: GroupAffine<Parameters>,
    lookup_grand_product_first_aggregated_commitment_coeff: Fr,
    pvs: PartialVerifierState,
    proof: Proof,
) {
    let queries_z_0 = queries.0;
    let queries_z_1 = queries.1;

    println!("Queries Z 0 x Slot: {:?}", queries_z_0.x.to_string());
    let mut aggregation_challenge = Fr::from_str("1").unwrap();

    let first_d_coeff: Fr;
    let first_t_coeff: Fr;

    let mut aggregated_at_z = queries_z_0;
    let proof_quotient_poly_opening_at_z_slot = proof.quotient_poly_opening_at_z;

    let state_v_slot = pvs.v;
    let proof_linearisation_poly_opening_at_z_slot = proof.linearisation_poly_opening_at_z;
    let proof_state_polys_0 = proof.state_poly_0;
    let proof_state_polys_1 = proof.state_poly_1;
    let proof_state_polys_2 = proof.state_poly_2;
    let state_opening_0_z = proof.state_poly_0_opening_at_z;
    let state_opening_1_z = proof.state_poly_1_opening_at_z;
    let state_opening_2_z = proof.state_poly_2_opening_at_z;
    let state_opening_3_z = proof.state_poly_3_opening_at_z;
    let proof_gate_selectors_0_opening_at_z = proof.gate_selectors_0_opening_at_z;
    let proof_copy_permutation_polys_0_opening_at_z = proof.copy_permutation_polys_0_opening_at_z;
    let proof_copy_permutation_polys_1_opening_at_z = proof.copy_permutation_polys_1_opening_at_z;
    let proof_copy_permutation_polys_2_opening_at_z = proof.copy_permutation_polys_2_opening_at_z;
    let proof_lookup_t_poly_opening_at_z = proof.lookup_t_poly_opening_at_z;
    let proof_lookup_selector_poly_opening_at_z = proof.lookup_selector_poly_opening_at_z;
    let proof_lookup_table_type_poly_opening_at_z = proof.lookup_table_type_poly_opening_at_z;

    let mut aggregated_opening_at_z = proof_quotient_poly_opening_at_z_slot;

    aggregated_at_z = aggregated_at_z.add(queries_z_1);
    aggregation_challenge = aggregation_challenge.mul(state_v_slot);

    aggregated_opening_at_z = aggregated_opening_at_z
        .add(aggregation_challenge.mul(proof_linearisation_poly_opening_at_z_slot));

    fn update_aggregation_challenge(
        queries_commitment_pt: GroupAffine<Parameters>,
        value_at_z: Fr,
        curr_aggregation_challenge: Fr,
        current_agg_opening_at_z: Fr,
        state_v_slot: Fr,
        aggregated_at_z: GroupAffine<Parameters>,
    ) -> (Fr, GroupAffine<Parameters>, Fr) {
        let mut new_agg_challenege = curr_aggregation_challenge.mul(state_v_slot);
        let new_aggregated_at_z = queries_commitment_pt
            .mul(new_agg_challenege)
            .into_affine()
            .add(aggregated_at_z);
        let new_agg_opening_at_z = new_agg_challenege
            .mul(value_at_z)
            .add(current_agg_opening_at_z);
        (
            new_agg_challenege,
            new_aggregated_at_z,
            new_agg_opening_at_z,
        )
    }

    let mut update_agg_challenge = update_aggregation_challenge(
        proof_state_polys_0,
        state_opening_0_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;

    println!("Aggregated at z 1 {:?}", aggregated_at_z.x.to_string());

    aggregation_challenge = update_agg_challenge.0;
    println!(
        "Aggregation Challenge 1 {:?}",
        aggregation_challenge.to_string()
    );
    aggregated_opening_at_z = update_agg_challenge.2;

    update_agg_challenge = update_aggregation_challenge(
        proof_state_polys_1,
        state_opening_1_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;
    println!("Aggregated at z 2 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 2 {:?}",
        aggregation_challenge.to_string()
    );

    update_agg_challenge = update_aggregation_challenge(
        proof_state_polys_2,
        state_opening_2_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;
    println!("Aggregated at z 3 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 3 {:?}",
        aggregation_challenge.to_string()
    );

    aggregation_challenge = aggregation_challenge.mul(state_v_slot);
    first_d_coeff = aggregation_challenge;

    aggregated_opening_at_z = aggregation_challenge
        .mul(state_opening_3_z)
        .add(aggregated_opening_at_z);

    update_agg_challenge = update_aggregation_challenge(
        vk_gate_selectors_0_affine,
        proof_gate_selectors_0_opening_at_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;

    println!("Aggregated at z 4 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 4 {:?}",
        aggregation_challenge.to_string()
    );

    update_agg_challenge = update_aggregation_challenge(
        vk_permutation_0_affine,
        proof_copy_permutation_polys_0_opening_at_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;

    println!("Aggregated at z 5 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 5 {:?}",
        aggregation_challenge.to_string()
    );

    update_agg_challenge = update_aggregation_challenge(
        vk_permutation_1_affine,
        proof_copy_permutation_polys_1_opening_at_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;

    println!("Aggregated at z 6 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 6 {:?}",
        aggregation_challenge.to_string()
    );

    update_agg_challenge = update_aggregation_challenge(
        vk_permutation_2_affine,
        proof_copy_permutation_polys_2_opening_at_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;

    println!("Aggregated at z 7 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 7 {:?}",
        aggregation_challenge.to_string()
    );

    aggregation_challenge = aggregation_challenge.mul(state_v_slot);
    first_t_coeff = aggregation_challenge;

    aggregated_opening_at_z = aggregation_challenge
        .mul(proof_lookup_t_poly_opening_at_z)
        .add(aggregated_opening_at_z);

    update_agg_challenge = update_aggregation_challenge(
        vk_lookup_selector_affine,
        proof_lookup_selector_poly_opening_at_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;

    println!("Aggregated at z 8 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 8 {:?}",
        aggregation_challenge.to_string()
    );

    update_agg_challenge = update_aggregation_challenge(
        vk_lookup_table_type_affine,
        proof_lookup_table_type_poly_opening_at_z,
        aggregation_challenge,
        aggregated_opening_at_z,
        state_v_slot,
        aggregated_at_z,
    );

    aggregated_at_z = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_at_z = update_agg_challenge.2;
    println!("Aggregated at z 9 {:?}", aggregated_at_z.x.to_string());
    println!(
        "Aggregation Challenge 9 {:?}",
        aggregation_challenge.to_string()
    );

    println!(
        "Aggregated Opening at Z x Slot: {:?}",
        aggregated_opening_at_z.to_string()
    );

    aggregation_challenge = aggregation_challenge.mul(state_v_slot);

    let state_u = pvs.u;

    let copy_permutation_coeff = aggregation_challenge
        .mul(state_u)
        .add(copy_permutation_first_aggregated_commitment_coeff);

    let proof_copy_permutation_grand_product_affine = proof.copy_permutation_grand_product;
    let proof_copy_permutation_grand_product_opening_at_z_omega = proof.copy_permutation_grand_product_opening_at_z_omega;

    let mut aggregated_z_omega = proof_copy_permutation_grand_product_affine
        .mul(copy_permutation_coeff)
        .into_affine();

    println!("Copy perm coeff {:?}", copy_permutation_coeff.to_string());
    println!(
        "Aggfldkhbldkghf Slot: {:?}",
        aggregated_z_omega.x.to_string()
    );

    let mut aggregated_opening_z_omega =
        proof_copy_permutation_grand_product_opening_at_z_omega.mul(aggregation_challenge);

    println!(
        "Aggregated Opening at Z Omega x Slot: {:?}",
        aggregated_opening_z_omega.to_string()
    );

    let proof_state_polys_3 = proof.state_poly_3;

    let proof_state_polys_3_opening_at_z_omega_slot = proof.state_poly_3_opening_at_z_omega;

    fn update_aggregation_challenge_second(
        queries_commitment_pt: GroupAffine<Parameters>,
        value_at_zomega: Fr,
        prev_coeff: Fr,
        curr_aggregation_challenge: Fr,
        current_aggregated_opening_z_omega: Fr,
        state_v_slot: Fr,
        state_u_slot: Fr,
        aggregated_at_z_omega: GroupAffine<Parameters>,
    ) -> (Fr, GroupAffine<Parameters>, Fr) {
        let new_aggregation_challenge = curr_aggregation_challenge.mul(state_v_slot);
        let final_coeff = new_aggregation_challenge.mul(state_u_slot).add(prev_coeff);
        let new_aggregated_at_z_omega = queries_commitment_pt
            .mul(final_coeff)
            .into_affine()
            .add(aggregated_at_z_omega);
        let new_aggregated_opening_at_z_omega = new_aggregation_challenge
            .mul(value_at_zomega)
            .add(current_aggregated_opening_z_omega);
        (
            new_aggregation_challenge,
            new_aggregated_at_z_omega,
            new_aggregated_opening_at_z_omega,
        )
    }

    update_agg_challenge = update_aggregation_challenge_second(
        proof_state_polys_3,
        proof_state_polys_3_opening_at_z_omega_slot,
        first_d_coeff,
        aggregation_challenge,
        aggregated_opening_z_omega,
        state_v_slot,
        state_u,
        aggregated_z_omega,
    );

    aggregated_z_omega = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_z_omega = update_agg_challenge.2;

    println!(
        "Aggregated at z omega 1 {:?}",
        aggregated_z_omega.x.to_string()
    );
    println!(
        "Aggregation Challenge 1 {:?}",
        aggregation_challenge.to_string()
    );

    let proof_lookup_s_poly = proof.lookup_s_poly;
    let proof_lookup_s_poly_opening_at_z_omega = proof.lookup_s_poly_opening_at_z_omega;
    let proof_lookup_grand_product_affine = proof.lookup_grand_product;

    update_agg_challenge = update_aggregation_challenge_second(
        proof_lookup_s_poly,
        proof_lookup_s_poly_opening_at_z_omega,
        lookup_s_first_aggregated_commitment_coeff,
        aggregation_challenge,
        aggregated_opening_z_omega,
        state_v_slot,
        state_u,
        aggregated_z_omega,
    );

    aggregated_z_omega = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_z_omega = update_agg_challenge.2;

    println!(
        "Aggregated at z omega 2 {:?}",
        aggregated_z_omega.x.to_string()
    );
    println!(
        "Aggregation Challenge 2 {:?}",
        aggregation_challenge.to_string()
    );

    let proof_lookup_grand_product_opening_at_z_omega = proof.lookup_grand_product_opening_at_z_omega;
    let proof_lookup_t_poly_opening_at_z_omega = proof.lookup_t_poly_opening_at_z_omega;
    update_agg_challenge = update_aggregation_challenge_second(
        proof_lookup_grand_product_affine,
        proof_lookup_grand_product_opening_at_z_omega,
        lookup_grand_product_first_aggregated_commitment_coeff,
        aggregation_challenge,
        aggregated_opening_z_omega,
        state_v_slot,
        state_u,
        aggregated_z_omega,
    );

    aggregated_z_omega = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_z_omega = update_agg_challenge.2;

    println!(
        "kdfghfgh {:?}",
        lookup_grand_product_first_aggregated_commitment_coeff.to_string()
    );

    println!(
        "Aggregated at z omega 3 {:?}",
        aggregated_z_omega.x.to_string()
    );
    println!(
        "Aggregation Challenge 3 {:?}",
        aggregation_challenge.to_string()
    );

    update_agg_challenge = update_aggregation_challenge_second(
        queries_t_poly_aggregated,
        proof_lookup_t_poly_opening_at_z_omega,
        first_t_coeff,
        aggregation_challenge,
        aggregated_opening_z_omega,
        state_v_slot,
        state_u,
        aggregated_z_omega,
    );

    aggregated_z_omega = update_agg_challenge.1;
    aggregation_challenge = update_agg_challenge.0;
    aggregated_opening_z_omega = update_agg_challenge.2;

    println!(
        "Aggregated at z omega 4 {:?}",
        aggregated_z_omega.x.to_string()
    );
    println!(
        "Aggregation Challenge 4 {:?}",
        aggregation_challenge.to_string()
    );

    // store aggregated_opening_z_omega somewhere and return it as it might be used somewhere else

    println!(
        "Aggregated at z x Slot: {:?}",
        aggregated_at_z.x.to_string()
    );

    println!(
        "Aggregated Z Omega x Slot: {:?}",
        aggregated_z_omega.x.to_string()
    );

    let pairing_pair_with_generator = aggregated_at_z.add(aggregated_z_omega);

    println!(
        "Pairing Pair with Generator x Slot: {:?}",
        pairing_pair_with_generator.x.to_string()
    );

    let aggregated_value = aggregated_opening_z_omega
        .mul(state_u)
        .add(aggregated_opening_at_z);

    println!(
        "Aggregated Value x Slot: {:?}",
        aggregated_value.to_string()
    );
}

pub struct Transcript {
    state_0: [u8; 32], // bytes32 in Solidity is equivalent to an array of 32 bytes in Rust
    state_1: [u8; 32], // Similarly, bytes32 translates to [u8; 32] in Rust
    challenge_counter: u32, // uint32 in Solidity is equivalent to u32 in Rust
    FR_MASK: Fp256<FrParameters>,
    DST_0: u32,
    DST_1: u32,
    DST_CHALLENGE: u32,
}

impl Transcript {
    fn new_transcript() -> Self {
        Transcript {
            state_0: [0; 32],     // Initializes state_0 with 32 bytes of zeros
            state_1: [0; 32],     // Initializes state_1 with 32 bytes of zeros
            challenge_counter: 0, // Initializes challenge_counter to 0
            FR_MASK: Fr::from_str(
                "14474011154664524427946373126085988481658748083205070504932198000989141204991",
            )
            .unwrap(),
            DST_0: 0,
            DST_1: 1,
            DST_CHALLENGE: 2,
        }
    }
    pub fn update_transcript(&mut self, value: &[u8]) {
        let mut transcript = Keccak::v256();

        // Simulate DST_0 and DST_1 as part of the transcript. In a real scenario,
        // these would be properly defined and included as per your protocol's design.
        let dst_0: u8 = 0;
        let dst_1: u8 = 1;

        // Update the transcript with DST_0 and the value, then hash it for newState0
        let val_beg = padd_bytes3(0u8.to_be_bytes().to_vec());
        let val_dst = (dst_0.to_be_bytes().to_vec());
        let val_s0 = padd_bytes32(self.state_0.to_vec());
        let val_s1 = padd_bytes32(self.state_1.to_vec());
        let val_chall = padd_bytes32(value.to_vec());

        let mut concatenated = Vec::new();
        concatenated.extend_from_slice(&val_beg);
        concatenated.extend_from_slice(&val_dst);
        concatenated.extend_from_slice(&val_s0);
        concatenated.extend_from_slice(&val_s1);
        concatenated.extend_from_slice(&val_chall);
        transcript.update(&concatenated);
        let mut out = [0u8; 32];
        transcript.finalize(&mut out);
        let newState0 = out;

        let newState0val = BigInt::from_bytes_be(Sign::Plus, &newState0);
        transcript = Keccak::v256();

        let val_beg = padd_bytes3(0u8.to_be_bytes().to_vec());
        let val_dst1 = (dst_1.to_be_bytes().to_vec());
        let val_s0 = padd_bytes32(self.state_0.to_vec());
        let val_s1 = padd_bytes32(self.state_1.to_vec());
        let val_chall = padd_bytes32(value.to_vec());

        let mut concatenated = Vec::new();
        concatenated.extend_from_slice(&val_beg);
        concatenated.extend_from_slice(&val_dst1);
        concatenated.extend_from_slice(&val_s0);
        concatenated.extend_from_slice(&val_s1);
        concatenated.extend_from_slice(&val_chall);
        transcript.update(&concatenated);

        let mut out = [0u8; 32];
        transcript.finalize(&mut out);
        let newState1 = out;
        let newState1val = BigInt::from_bytes_be(Sign::Plus, &out);
        // println!("newState1: {:?}", newState1val);

        // Update the state fields with the new hashed states
        self.state_0.copy_from_slice(&newState0);
        self.state_1.copy_from_slice(&newState1);
    }

    pub fn get_transcript_challenge(&mut self, number_of_challenge: u32) -> [u8; 32] {
        let mut transcript = Keccak::v256();

        let val_beg = padd_bytes3(0u8.to_be_bytes().to_vec());
        let val_dst2 = 2u8.to_be_bytes().to_vec();
        let val_s0 = self.state_0.to_vec();
        let val_s1 = self.state_1.to_vec();
        // chall
        let temp_chall = BigInt::from(number_of_challenge).mul(BigInt::from(2).pow(224));
        let mut val_chall = padd_bytes32(temp_chall.to_bytes_be().1);
        let final_val_chall = &val_chall[0..4];

        // println!("final_val_chall: {:?}", final_val_chall);

        let mut concatenated = Vec::new();
        concatenated.extend_from_slice(&val_beg);
        concatenated.extend_from_slice(&val_dst2);
        concatenated.extend_from_slice(&val_s0);
        concatenated.extend_from_slice(&val_s1);
        concatenated.extend_from_slice(&final_val_chall);
        transcript.update(&concatenated);

        let mut out = [0u8; 32];
        transcript.finalize(&mut out);
        let res = BigInt::from_bytes_be(Sign::Plus, &out);

        const FR_MASK: [u8; 32] = [
            0x1f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff,
        ];
        let mut res_fr = [0u8; 32];
        for i in 0..32 {
            res_fr[i] = out[i] & FR_MASK[i];
        }

        res_fr
    }
}

pub fn getPublicInputs() -> Fp256<FrParameters> {
    let ttt = get_fr_mask().into_repr().0[0] & get_fr_mask().into_repr().0[1];
    let pi = Fr::from_str("7930533175376274174682760122775727104792125867965765072731098693082")
        .unwrap();
    let mut res = apply_fr_mask(padd_bytes32(get_u8arr_from_fr(pi)));
    get_fr_from_u8arr(res)
}

pub fn get_fr_mask() -> Fp256<FrParameters> {
    Fr::from_str("14474011154664524427946373126085988481658748083205070504932198000989141204991")
        .unwrap()
}

pub fn get_domain_size() -> u64 {
    16777216
}

pub fn get_scalar_field() -> Fp256<FrParameters> {
    Fr::from_str("21888242871839275222246405745257275088548364400416034343698204186575808495617")
        .unwrap()
}

pub fn get_omega() -> Fp256<FrParameters> {
    Fr::from_str("11451405578697956743456240853980216273390554734748796433026540431386972584651")
        .unwrap()
}

pub fn evaluate_lagrange_poly_out_of_domain(
    poly_num: u64,
    at: Fp256<FrParameters>,
) -> Fp256<FrParameters> {
    let mut omega_power = Fr::from_str("1").unwrap();
    if poly_num > 0 {
        omega_power = get_omega().pow(&[poly_num as u64]);
    }
    println!("omegaPower: {}", omega_power);
    let mut res = at
        .pow(&[get_domain_size()])
        .add(get_scalar_field().sub(Fr::from_str("1").unwrap()));
    assert_ne!(res, Fp256::zero());

    res = res.mul(omega_power);

    let mut denominator = at.add(get_scalar_field().sub((Fr::from(omega_power))));
    denominator = denominator.mul(Fr::from(get_domain_size()));
    denominator = denominator.inverse().unwrap();
    res = res.mul(denominator);

    res
}

pub fn permutation_quotient_contribution(
    pvs: &mut PartialVerifierState,
    l0AtZ: Fp256<FrParameters>,
) -> Fp256<FrParameters> {
    let mut res = pvs
        .power_of_alpha_4
        .mul(get_proof().copy_permutation_grand_product_opening_at_z_omega);
    let mut factor_multiplier;

    factor_multiplier = get_proof()
        .copy_permutation_polys_0_opening_at_z
        .mul(pvs.beta);
    factor_multiplier = factor_multiplier.add(pvs.gamma);
    factor_multiplier = factor_multiplier.add(get_proof().state_poly_0_opening_at_z);
    res = res.mul(factor_multiplier);

    factor_multiplier = get_proof()
        .copy_permutation_polys_1_opening_at_z
        .mul(pvs.beta);
    factor_multiplier = factor_multiplier.add(pvs.gamma);
    factor_multiplier = factor_multiplier.add(get_proof().state_poly_1_opening_at_z);
    res = res.mul(factor_multiplier);

    factor_multiplier = get_proof()
        .copy_permutation_polys_2_opening_at_z
        .mul(pvs.beta);
    factor_multiplier = factor_multiplier.add(pvs.gamma);
    factor_multiplier = factor_multiplier.add(get_proof().state_poly_2_opening_at_z);
    res = res.mul(factor_multiplier);

    res = res.mul(get_proof().state_poly_3_opening_at_z.add(pvs.gamma));
    res = get_scalar_field().sub(res);

    let mut temp_l0atz = l0AtZ.clone();
    temp_l0atz = temp_l0atz.mul(pvs.power_of_alpha_5);
    res = res.add(temp_l0atz.neg());

    res
}

pub fn lookup_quotient_contribution(pvs: &mut PartialVerifierState) -> Fp256<FrParameters> {
    let betaplusone = pvs.beta_lookup.add(Fr::from_str("1").unwrap());
    let beta_gamma = betaplusone.mul(pvs.gamma_lookup);

    pvs.beta_gamma_plus_gamma = beta_gamma;

    let mut res = get_proof()
        .lookup_s_poly_opening_at_z_omega
        .mul(pvs.beta_lookup);
    res = res.add(beta_gamma);
    res = res.mul(get_proof().lookup_grand_product_opening_at_z_omega);
    res = res.mul(pvs.power_of_alpha_6);

    let mut last_omega = get_omega().pow([get_domain_size() - 1]);
    println!("lastOmega: {}", get_bigint_from_fr(last_omega));
    let z_minus_last_omega = pvs.z.add(last_omega.neg());
    res = res.mul(z_minus_last_omega);

    let intermediate_value = pvs.l_0_at_z.mul(pvs.power_of_alpha_7);
    res = res.add(intermediate_value.neg());

    let beta_gamma_powered = beta_gamma.pow([get_domain_size() - 1]);
    let subtrahend = pvs
        .power_of_alpha_8
        .mul(pvs.l_n_minus_one_at_z.mul(beta_gamma_powered));
    res = res.add(subtrahend.neg());
    println!("res: {}", get_bigint_from_fr(res));
    res
}

pub fn verify_quotient_evaluation(pvs: &mut PartialVerifierState) {
    let l0atz = evaluate_lagrange_poly_out_of_domain(0, pvs.z);
    let lnmius1at_z = evaluate_lagrange_poly_out_of_domain(get_domain_size() - 1, pvs.z);
    pvs.l_0_at_z = l0atz;
    pvs.l_n_minus_one_at_z = lnmius1at_z;

    let state_t = l0atz.mul(getPublicInputs());
    let mut result = state_t.mul(get_proof().gate_selectors_0_opening_at_z);
    result = result.add(permutation_quotient_contribution(pvs, l0atz));

    result = result.add(lookup_quotient_contribution(pvs));
    result = result.add(get_proof().linearisation_poly_opening_at_z);

    let vanishing = pvs.z_in_domain_size.add(Fr::from_str("1").unwrap().neg());
    let lhs = get_proof().quotient_poly_opening_at_z.mul(vanishing);

    assert_eq!(lhs, result);
}

pub fn get_challenges(pvs: &mut PartialVerifierState) {
    let mut transcript = Transcript::new_transcript();

    transcript.update_transcript(&get_u8arr_from_fr(getPublicInputs()));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_0.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_0.y));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_1.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_1.y));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_2.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_2.y));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_3.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().state_poly_3.y));

    let etaaa = transcript.get_transcript_challenge(0);
    println!("etaaa: {}", BigInt::from_bytes_be(Sign::Plus, &etaaa));

    transcript.update_transcript(&get_u8arr_from_fq(get_proof().lookup_s_poly.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().lookup_s_poly.y));

    let betaa = transcript.get_transcript_challenge(1);
    let gammma = transcript.get_transcript_challenge(2);
    println!("betaa: {}", BigInt::from_bytes_be(Sign::Plus, &betaa));
    println!("gammma: {}", BigInt::from_bytes_be(Sign::Plus, &gammma));

    transcript.update_transcript(&get_u8arr_from_fq(
        get_proof().copy_permutation_grand_product.x,
    ));
    transcript.update_transcript(&get_u8arr_from_fq(
        get_proof().copy_permutation_grand_product.y,
    ));

    let beta_lookuppp = transcript.get_transcript_challenge(3);
    let gamma_lookuppp = transcript.get_transcript_challenge(4);
    println!(
        "beta_lookuppp: {}",
        BigInt::from_bytes_be(Sign::Plus, &beta_lookuppp)
    );
    println!(
        "gamma_lookuppp: {}",
        BigInt::from_bytes_be(Sign::Plus, &gamma_lookuppp)
    );

    transcript.update_transcript(&get_u8arr_from_fq(get_proof().lookup_grand_product.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().lookup_grand_product.y));

    let alphaaa = transcript.get_transcript_challenge(5);
    println!("alphaaa: {}", BigInt::from_bytes_be(Sign::Plus, &alphaaa));

    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_0.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_0.y));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_1.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_1.y));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_2.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_2.y));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_3.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().quotient_poly_parts_3.y));

    let zz = transcript.get_transcript_challenge(6);
    let zz_in_domain_size = get_fr_from_u8arr(zz.to_vec()).pow([get_domain_size()]);
    println!("zz: {}", BigInt::from_bytes_be(Sign::Plus, &zz));
    println!(
        "zz_in_domain_size: {}",
        get_bigint_from_fr(zz_in_domain_size)
    );

    transcript.update_transcript(&get_u8arr_from_fr(get_proof().quotient_poly_opening_at_z));

    transcript.update_transcript(&get_u8arr_from_fr(get_proof().state_poly_0_opening_at_z));
    transcript.update_transcript(&get_u8arr_from_fr(get_proof().state_poly_1_opening_at_z));
    transcript.update_transcript(&get_u8arr_from_fr(get_proof().state_poly_2_opening_at_z));
    transcript.update_transcript(&get_u8arr_from_fr(get_proof().state_poly_3_opening_at_z));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().state_poly_3_opening_at_z_omega,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().gate_selectors_0_opening_at_z,
    ));

    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().copy_permutation_polys_0_opening_at_z,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().copy_permutation_polys_1_opening_at_z,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().copy_permutation_polys_2_opening_at_z,
    ));

    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().copy_permutation_grand_product_opening_at_z_omega,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(get_proof().lookup_t_poly_opening_at_z));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().lookup_selector_poly_opening_at_z,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().lookup_table_type_poly_opening_at_z,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().lookup_s_poly_opening_at_z_omega,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().lookup_grand_product_opening_at_z_omega,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().lookup_t_poly_opening_at_z_omega,
    ));
    transcript.update_transcript(&get_u8arr_from_fr(
        get_proof().linearisation_poly_opening_at_z,
    ));

    let vv = transcript.get_transcript_challenge(7);
    println!("vv: {}", BigInt::from_bytes_be(Sign::Plus, &vv));

    transcript.update_transcript(&get_u8arr_from_fq(get_proof().opening_proof_at_z.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().opening_proof_at_z.y));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().opening_proof_at_z_omega.x));
    transcript.update_transcript(&get_u8arr_from_fq(get_proof().opening_proof_at_z_omega.y));

    let uu = transcript.get_transcript_challenge(8);
    println!("uu: {}", BigInt::from_bytes_be(Sign::Plus, &uu));

    let power_of_alpha_1 = get_fr_from_u8arr(alphaaa.to_vec());
    let power_of_alpha_2 = power_of_alpha_1.mul(power_of_alpha_1);
    let power_of_alpha_3 = power_of_alpha_2.mul(power_of_alpha_1);
    let power_of_alpha_4 = power_of_alpha_3.mul(power_of_alpha_1);
    let power_of_alpha_5 = power_of_alpha_4.mul(power_of_alpha_1);
    let power_of_alpha_6 = power_of_alpha_5.mul(power_of_alpha_1);
    let power_of_alpha_7 = power_of_alpha_6.mul(power_of_alpha_1);
    let power_of_alpha_8 = power_of_alpha_7.mul(power_of_alpha_1);

    pvs.alpha = power_of_alpha_1;
    pvs.beta = get_fr_from_u8arr(betaa.to_vec());
    pvs.gamma = get_fr_from_u8arr(gammma.to_vec());
    pvs.power_of_alpha_2 = power_of_alpha_2;
    pvs.power_of_alpha_3 = power_of_alpha_3;
    pvs.power_of_alpha_4 = power_of_alpha_4;
    pvs.power_of_alpha_5 = power_of_alpha_5;
    pvs.power_of_alpha_6 = power_of_alpha_6;
    pvs.power_of_alpha_7 = power_of_alpha_7;
    pvs.power_of_alpha_8 = power_of_alpha_8;
    pvs.eta = get_fr_from_u8arr(etaaa.to_vec());
    pvs.beta_lookup = get_fr_from_u8arr(beta_lookuppp.to_vec());
    pvs.gamma_lookup = get_fr_from_u8arr(gamma_lookuppp.to_vec());
    pvs.beta_plus_one = pvs.beta_lookup.add(Fr::from_str("1").unwrap());
    pvs.beta_gamma_plus_gamma = pvs.beta_lookup.add(Fr::from_str("1").unwrap()).mul(pvs.gamma_lookup);
    pvs.v = get_fr_from_u8arr(vv.to_vec());
    pvs.u = get_fr_from_u8arr(uu.to_vec());
    pvs.z = get_fr_from_u8arr(zz.to_vec());
    pvs.z_minus_last_omega = pvs.z.add(get_omega().pow([get_domain_size() - 1]).neg());
    pvs.z_in_domain_size = zz_in_domain_size;
}

pub fn get_u8arr_from_fq(fq: Fp256<FqParameters>) -> Vec<u8> {
    let mut st = fq.to_string();
    let temp = &st[8..8 + 64];
    BigInt::parse_bytes(temp.as_bytes(), 16)
        .unwrap()
        .to_bytes_be()
        .1
}

pub fn get_u8arr_from_fr(fr: Fp256<FrParameters>) -> Vec<u8> {
    get_bigint_from_fr(fr).to_bytes_be().1
}

pub fn get_fr_from_u8arr(arr: Vec<u8>) -> Fp256<FrParameters> {
    let temp = BigInt::from_bytes_be(Sign::Plus, &arr);
    Fr::from_str(&temp.to_string()).unwrap()
}

pub fn get_bigint_from_fr(fr: Fp256<FrParameters>) -> BigInt {
    let mut st = fr.to_string();
    let temp = &st[8..8 + 64];
    BigInt::parse_bytes(temp.as_bytes(), 16).unwrap()
}

pub fn padd_bytes32(input: Vec<u8>) -> Vec<u8> {
    let mut result = input.clone();
    let mut padding = vec![0; 32 - input.len()];
    padding.append(&mut result);
    padding
}

pub fn padd_bytes3(input: Vec<u8>) -> Vec<u8> {
    let mut result = input.clone();
    let mut padding = vec![0; 3 - input.len()];
    padding.append(&mut result);
    padding
}

pub fn apply_fr_mask(out: Vec<u8>) -> Vec<u8> {
    const FR_MASK: [u8; 32] = [
        0x1f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff,
    ];
    let mut res_fr = [0u8; 32];

    for i in 0..32 {
        res_fr[i] = out[i] & FR_MASK[i];
    }

    res_fr.to_vec()
}

