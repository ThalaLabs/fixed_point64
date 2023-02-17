#[test_only]
module fixed_point64::log_exp_math_tests {
    use fixed_point64::fixed_point64;
    use fixed_point64::log_exp_math;
    

    #[test]
    fun test_exp_close_to_1() {
        let x = fixed_point64::fraction(10000000001, 10000000000);
        let (sign, result_1) = log_exp_math::ln(x);
        assert!(sign == 1, 0);

        let y = fixed_point64::fraction(10000000000, 10000000000);
        let (sign, result_2) = log_exp_math::ln(y);
        assert!(sign == 1, 0);

        assert!(!fixed_point64::eq(&result_1, &result_2), 0);
    }

    #[test]
    fun test_log2_sqrt_2() {
        let x = fixed_point64::fraction(1414213562, 1000000000);
        let (sign, result) = log_exp_math::log2(x);
        assert!(sign == 1, 0);
        
        assert!(fixed_point64::to_u128(result) == 9223372029833779420, 1); // approx 0.5
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
        
        assert!(fixed_point64::to_u128(result) == 9223372043875772196, 1); // approx 0.5
    }
    
    #[test]
    fun test_log2_e() {
        let x = fixed_point64::fraction(2718281828459, 1000000000000);
        let (sign, result) = log_exp_math::log2(x);
        assert!(sign == 1, 0);
        
        assert!(fixed_point64::to_u128(result) == 26613026195688202108, 1);
    }
    
    #[test]
    fun test_ln_e() {
        let x = fixed_point64::fraction(2718281828459, 1000000000000);
        let (sign, result) = log_exp_math::ln(x);
        assert!(sign == 1, 0);
        
        assert!(fixed_point64::to_u128(result) == 18446744074827235266, 1); // approx 1.0
    }

    #[test]
    fun test_ln_sqrt_e() {
        let x = fixed_point64::fraction(1648721271, 1000000000);
        let (sign, result) = log_exp_math::ln(x);
        assert!(sign == 1, 0);
        
        assert!(fixed_point64::to_u128(result) == 9223372040768892103, 1); // approx 0.5
    }
    
    #[test]
    fun test_exp_0() {
        let x = fixed_point64::zero();
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == 1 << 64, 1);
    }
    
    #[test]
    fun test_exp_1() {
        let e = fixed_point64::fraction(2718281828459045235, 1000000000000000000);
        let x = fixed_point64::one();
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == fixed_point64::to_u128(e), 1);
    }

    #[test]
    fun test_exp_2() {
        let e = fixed_point64::fraction(2718281828459045235, 1000000000000000000);
        let x = fixed_point64::encode(2);
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == fixed_point64::to_u128(fixed_point64::mul_fp(e, e)), 1);
    }
    
    #[test]
    fun test_exp_3() {
        let x = fixed_point64::encode(3);
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == 370512759205086491192, 1);
    }

    #[test]
    fun test_exp_1_over_2() {
        let x = fixed_point64::fraction(1, 2);
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == 30413539329486470297, 1);
    }

    #[test]
    fun test_exp_1_over_3() {
        let x = fixed_point64::fraction(1, 3);
        let result = log_exp_math::exp(1, x);
        assert!(fixed_point64::to_u128(result) == 25744505231652237576, 1); // e^(1/3) = 1.39561242462
    }
    
    #[test]
    fun test_exp_neg_1() {
        let e = fixed_point64::fraction(2718281828459045235, 1000000000000000000);
        let e_inv = fixed_point64::div_fp(fixed_point64::one(), e);
        let x = fixed_point64::one();
        let result = log_exp_math::exp(0, x);
        assert!(fixed_point64::to_u128(result) == fixed_point64::to_u128(e_inv), 1);
    }

    #[test]
    fun test_exp_neg_1_over_3() {
        let x = fixed_point64::fraction(1, 3);
        let result = log_exp_math::exp(0, x);
        assert!(fixed_point64::to_u128(result) == 13217669704916664320, 1); // e^(-1/3) = 0.71653131
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
        assert!(fixed_point64::to_u128(result) == 8868269569660157952, 1); // (1/3)^(2/3) = 0.4807498568

        let scale_up = fixed_point64::fraction(1000000001, 1000000000);
        let result = log_exp_math::pow_up(x, y);
        assert!(fixed_point64::eq(&result, &fixed_point64::mul_fp(fixed_point64::from_u128(8868269569660157952), scale_up)), 1);

        let result = log_exp_math::pow_down(x, y);
        let scale_down = fixed_point64::fraction(999999999, 1000000000);
        assert!(fixed_point64::eq(&result, &fixed_point64::mul_fp(fixed_point64::from_u128(8868269569660157952), scale_down)), 1);
    }

    #[test]
    fun test_pow_large_number() {
        let max_u64_u128: u128 = 1 << 64 - 1;
        let max_u64: u64 = (max_u64_u128 as u64);
        let max_u64_fp = fixed_point64::encode(max_u64);
        let a = fixed_point64::fraction(1, 8);
        let b = fixed_point64::encode(8);
        let result_up = log_exp_math::pow_up(log_exp_math::pow_up(max_u64_fp, a), b);
        let result_down = log_exp_math::pow_down(log_exp_math::pow_down(max_u64_fp, a), b);

        assert!(fixed_point64::gte(&result_up, &max_u64_fp), 1);
        assert!(fixed_point64::lte(&result_down, &max_u64_fp), 1);
    }
}