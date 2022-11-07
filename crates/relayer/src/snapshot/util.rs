use bigdecimal::BigDecimal;

pub fn bigdecimal_to_u64(b: BigDecimal) -> u64 {
    assert!(b.is_integer());

    let (bigint, _) = b.as_bigint_and_exponent();
    let (sign, digits) = bigint.to_u64_digits();

    assert!(sign == bigdecimal::num_bigint::Sign::Plus);
    assert!(digits.len() == 1);

    digits[0]
}
