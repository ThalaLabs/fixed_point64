#[test_only]
module fixed_point64::log_exp_math_tests {
    use fixed_point64::fixed_point64;
    use fixed_point64::log_exp_math;

    const EXP_1_RAW: u128 = 50143449209799256682;
    const EXP_2_RAW: u128 = 136304026803256390412;
    const EXP_4_RAW: u128 = 1007158100559408451354;

    const EXP_1_OVER_2_RAW: u128 = 30413539329486470296;
    const EXP_1_OVER_4_RAW: u128 = 23686088245777032824;
    

    #[test]
    #[expected_failure(abort_code = log_exp_math::ERR_LOG_EXP_MATH_LOG_2_ZERO_UNBOUNDED)]
    fun test_log2_zero() {
        // If abort not present log2(0) will timeout
        let x = fixed_point64::zero();
        let (_, _) = log_exp_math::log2(x);
    }

    #[test]
    fun test_log2_sqrt_2() {
        let x = fixed_point64::fraction(1414213562, 1000000000);
        let (sign, result) = log_exp_math::log2(x);
        assert!(sign == 1, 0);

        assert!(fixed_point64::to_u128(result) == 9223372029833779422, 1); // approx 0.5
    }
    
    #[test]
    fun test_log2_4() {
        let x = fixed_point64::encode(4);
        let (sign, result) = log_exp_math::log2(x);
        assert!(sign == 1, 0);
        
        assert!(fixed_point64::to_u128(result) == 36893488147419103232, 1); // approx 2.0
    }
    
    #[test]
    fun test_log2_half_sqrt_2() {
        let x = fixed_point64::fraction(707106781, 1000000000);
        let (sign, result) = log_exp_math::log2(x);
        assert!(sign == 0, 0);
        
        assert!(fixed_point64::to_u128(result) == 9223372043875772194, 1); // approx 0.5
    }
    
    #[test]
    fun test_log2_e() {
        let x = fixed_point64::fraction(2718281828459, 1000000000000);
        let (sign, result) = log_exp_math::log2(x);
        assert!(sign == 1, 0);

        assert!(fixed_point64::to_u128(result) == 26613026195688202110, 1);
    }

    #[test]
    fun test_ln_close_to_1() {
        let x = fixed_point64::fraction(10000000001, 10000000000);
        let (sign, result_1) = log_exp_math::ln(x);
        assert!(sign == 1, 0);

        let y = fixed_point64::fraction(10000000000, 10000000000);
        let (sign, result_2) = log_exp_math::ln(y);
        assert!(sign == 1, 0);

        assert!(!fixed_point64::eq(&result_1, &result_2), 0);
    }

    #[test]
    fun test_ln_e() {
        let x = fixed_point64::fraction(2718281828459, 1000000000000);
        let (sign, result) = log_exp_math::ln(x);
        assert!(sign == 1, 0);

        assert!(fixed_point64::to_u128(result) == 18446744073709244638, 1); // approx 1.0 (0.999999999999983358)
    }

    #[test]
    fun test_ln_sqrt_e() {
        let x = fixed_point64::fraction(1648721271, 1000000000);
        let (sign, result) = log_exp_math::ln(x);
        assert!(sign == 1, 0);

        assert!(fixed_point64::to_u128(result) == 9223372040209896788, 1); // approx 0.5 (0.500000000181881)
    }

    #[test]
    fun test_ln_very_small() {
        // ln(1/2^64) = -44.361419555836499_802
        let x = fixed_point64::from_u128(1);
        let (sign, result) = log_exp_math::ln(x);
        assert!(sign == 0, 0);

        // -44.361419555836499_799
        assert!(fixed_point64::to_u128(result) == 818323753292969962176, 1);
    }

    #[test]
    fun test_ln_one_plus_eps() {
        let x = fixed_point64::fraction(1000000001, 1000000000); // 1 + 1e-9
        let (_, result) = log_exp_math::ln(x);
        // ln(1 + 1e-9) = 0.000000000999999999_5
        // 0.000000000999999999_36
        assert!(fixed_point64::to_u128(result) == 18446744062, 1);
    }
    
    #[test]
    fun test_exp_0() {
        let x = fixed_point64::zero();
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == 1 << 64, 1);
    }
    
    #[test]
    fun test_exp_1() {
        let e = fixed_point64::from_u128(EXP_1_RAW);
        let x = fixed_point64::one();
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == fixed_point64::to_u128(e), 1);
    }

    #[test]
    fun test_exp_2() {
        let e = fixed_point64::from_u128(EXP_1_RAW);
        let x = fixed_point64::encode(2);
        let result = log_exp_math::exp(1, x);
        // e does not have sufficient precision to represent result exactly accurately. For this reason we use a tolerance of 2e-19
        let tolerance = 4;
        assert!(fixed_point64::to_u128(result) == fixed_point64::to_u128(fixed_point64::mul_fp(e, e)) + tolerance, 1);
    }


    #[test]
    fun test_exp_3() {
        // e^3 = 20.085536923187667740
        let x = fixed_point64::encode(3);
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == 370512759205086491340, 1); // 20.085536923187667740
    }

    #[test]
    fun test_exp_1_over_2() {
        let x = fixed_point64::fraction(1, 2);
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == EXP_1_OVER_2_RAW, 1);
    }

    #[test]
    fun test_exp_1_over_3() {
        let x = fixed_point64::fraction(1, 3);
        let result = log_exp_math::exp(1, x);
        // e^(1/3) = 1.3956124250860895286_28
        assert!(fixed_point64::to_u128(result) == 25744505231652237578, 1); // 1.3956124250860895286_01
    }
    
    #[test]
    fun test_exp_neg_1() {
        let e = fixed_point64::from_u128(EXP_1_RAW);
        let e_inv = fixed_point64::div_fp(fixed_point64::one(), e);
        let x = fixed_point64::one();
        let result = log_exp_math::exp(0, x);
        assert!(fixed_point64::to_u128(result) == fixed_point64::to_u128(e_inv), 1);
    }

    #[test]
    fun test_exp_neg_1_over_3() {
        let x = fixed_point64::fraction(1, 3);
        let result = log_exp_math::exp(0, x);
        // e^(-1/3) = 0.7165313105737892504_256
        assert!(fixed_point64::to_u128(result) == 13217669706954385034, 1); // 0.7165313105737892504_379
    }

    // #[test]
    // fun test_exp_max_safe() {
    //     // NOTE: "exp" asserts that x < TWO_POW_6_RAW
    //     // - In actuality, exp begins to fail when x >= TWO_POW_RAW_6 - 100000000000000000000
    //     // TODO: Decide how to handle this
    //     let x = fixed_point64::from_u128((1 << 70) - 1000000000000000000000);
    //     let result = log_exp_math::exp(1, x);
    //     assert!(fixed_point64::to_u128(result) == 0, 0);
    // }

    #[test]
    fun test_exp_ln_inverse() {
        // e^2 should be: 136304026803256390412
        // with precision limitations, e^2: 136304026803256390408
        let e_squared = fixed_point64::mul_fp(fixed_point64::from_u128(EXP_1_RAW), fixed_point64::from_u128(EXP_1_RAW));
        assert!(fixed_point64::to_u128(e_squared) == 136304026803256390408, 0);

        // ln(e^2) should be 2
        // with precision limitations, ln(e^2) = 1.99999999999999999996
        let (sign, ln_e2) = log_exp_math::ln(e_squared);

        // e^(ln(e^2)) should be e^2
        // with precision limitations, e^(ln(e^2)) is slightly lower
        let result = log_exp_math::exp(sign, ln_e2);
        assert!(fixed_point64::to_u128(e_squared) - fixed_point64::to_u128(result) < 10000, 0); // error of 0.00000000000005%
    }
    
    #[test]
    #[expected_failure(abort_code = log_exp_math::ERR_EXPONENT_TOO_LARGE)]
    fun test_exp_fail_too_large() {
        let x = fixed_point64::from_u128(1 << 70);
        log_exp_math::exp(1, x);
    }
    
    #[test]
    fun test_pow() {
        let x = fixed_point64::fraction(1, 3);
        let y = fixed_point64::fraction(2, 3);
        let result = log_exp_math::pow(x, y);

        // (1/3)^(2/3) = 0.48074985676913612744_05
        assert!(fixed_point64::to_u128(result) == 8868269571292777626, 1); // 0.48074985676913612744_29

        let scale_up = fixed_point64::fraction(1000000001, 1000000000);
        let result = log_exp_math::pow_up(x, y);
        assert!(fixed_point64::eq(&result, &fixed_point64::mul_fp(fixed_point64::from_u128(8868269571292777626), scale_up)), 1);

        let result = log_exp_math::pow_down(x, y);
        let scale_down = fixed_point64::fraction(999999999, 1000000000);
        assert!(fixed_point64::eq(&result, &fixed_point64::mul_fp(fixed_point64::from_u128(8868269571292777626), scale_down)), 1);
    }

    #[test]
    fun test_pow_large_number() {
        let max_u64_u128: u128 = 1 << 64 - 1;
        let max_u64: u64 = (max_u64_u128 as u64);
        let max_u64_fp = fixed_point64::encode(max_u64);

        // actual value of (MAX_U64 ^ (1/8)) ^ 8 is MAX_U64
        // test pow_up and pow_down are working properly
        let a = fixed_point64::fraction(1, 8);
        let b = fixed_point64::encode(8);
        let result_up = log_exp_math::pow_up(log_exp_math::pow_up(max_u64_fp, a), b);
        let result_down = log_exp_math::pow_down(log_exp_math::pow_down(max_u64_fp, a), b);

        assert!(fixed_point64::gte(&result_up, &max_u64_fp), 1);
        assert!(fixed_point64::lte(&result_down, &max_u64_fp), 1);
    }

    #[test]
    fun test_pow_zero_exp() {
        // All numbers to the power of 0 == 1
        let one = fixed_point64::one();
        assert!(fixed_point64::eq(&log_exp_math::pow(fixed_point64::zero(), fixed_point64::zero()), &one), 1);
        assert!(fixed_point64::eq(&log_exp_math::pow(fixed_point64::encode(100000), fixed_point64::zero()), &one), 1);
    }

    #[test]
    fun test_pow_zero_base() {
        let result = log_exp_math::pow(fixed_point64::zero(), fixed_point64::fraction(1, 2));
        assert!(fixed_point64::eq(&result, &fixed_point64::zero()), 1);
    }

    #[test]
    fun test_pow_bounds() {
        let x = fixed_point64::fraction(123456789, 100000000);
        let y = fixed_point64::fraction(987654321, 1000000000);

        let p_down = log_exp_math::pow_down(x, y);
        let p = log_exp_math::pow(x, y);
        let p_up = log_exp_math::pow_up(x, y);

        assert!(fixed_point64::lte(&p_down, &p), 1);
        assert!(fixed_point64::lte(&p, &p_up), 1);
    }

    #[test]
    fun test_pow_sqrt_highly_precise() {
        // sqrt(279681681134)
        let x = fixed_point64::encode(279681681134);
        let y = fixed_point64::fraction(1, 2);
        let result = log_exp_math::pow(x, y);

        // sqrt(279681681134) = 528849.393621662385659139_70
        assert!(fixed_point64::to_u128(result) == 9755549417675290558929646, 1); // 528849.393621662385659139_69

        // sqrt(53680401408637341)
        let x = fixed_point64::encode(53680401408637341);
        let y = fixed_point64::fraction(1, 2);

        let result = log_exp_math::pow(x, y);

        // sqrt(53680401408637341) = 231690313.583967814957765608_209
        assert!(fixed_point64::to_u128(result) == 4273931919040965914809974593, 1); // 231690313.583967814957765608_190
    }

    #[test]
    fun test_pow_sqrt() {
        let one_u256 = (1u256 << 128);
        let result = log_exp_math::sqrt(one_u256);
        assert!(result == 1 << 64, 0);
    }
}