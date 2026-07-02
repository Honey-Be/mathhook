//! Common factor extraction and GCD operations

use crate::core::{Expression, Number};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

impl Expression {
    /// Find common factor in a list of terms
    pub(super) fn find_common_factor_in_terms(&self, terms: &[Expression]) -> Expression {
        if terms.is_empty() {
            return Expression::integer(1);
        }

        let mut common = self.extract_factors(&terms[0]);

        for term in &terms[1..] {
            let term_factors = self.extract_factors(term);
            common = self.intersect_factors(&common, &term_factors);

            if common.is_empty() {
                return Expression::integer(1);
            }
        }

        if common.is_empty() {
            Expression::integer(1)
        } else {
            Expression::mul(common)
        }
    }

    /// Extract factors from an expression
    pub(super) fn extract_factors(&self, expr: &Expression) -> Vec<Expression> {
        match expr {
            Expression::Number(Number::Integer(n)) => {
                if !n.is_zero() && !n.is_one() {
                    vec![expr.clone()]
                } else {
                    vec![]
                }
            }
            Expression::Symbol(_) => vec![expr.clone()],
            Expression::Mul(factors) => (**factors).clone(),
            Expression::Pow(base, _exp) => vec![(**base).clone()],
            _ => vec![expr.clone()],
        }
    }

    /// Find intersection of two factor lists
    pub(super) fn intersect_factors(
        &self,
        factors1: &[Expression],
        factors2: &[Expression],
    ) -> Vec<Expression> {
        let mut common = Vec::new();

        for factor1 in factors1 {
            if factors2.contains(factor1) {
                common.push(factor1.clone());
            }
        }

        let num1 = self.extract_numeric_factor(factors1);
        let num2 = self.extract_numeric_factor(factors2);

        if let (Some(n1), Some(n2)) = (num1, num2) {
            let gcd_num = n1.gcd(&n2);
            if !gcd_num.is_one() {
                common.push(Expression::big_integer(gcd_num));
            }
        }

        common
    }

    /// Extract numeric factor from factor list
    pub(super) fn extract_numeric_factor(&self, factors: &[Expression]) -> Option<BigInt> {
        for factor in factors {
            if let Expression::Number(Number::Integer(n)) = factor {
                return Some(BigInt::from(*n));
            }
        }
        None
    }

    /// Divide expression by a factor (simplified division)
    pub(super) fn divide_by_factor(&self, expr: &Expression, factor: &Expression) -> Expression {
        // A composite (product) factor: divide by each of its components in turn,
        // e.g. `2x² ÷ 2x = x`. Peeling one component at a time reuses the atomic
        // cases below and keeps the product invariant `factored · factor = expr`.
        if let Expression::Mul(components) = factor {
            let mut acc = expr.clone();
            for component in components.iter() {
                acc = self.divide_by_factor(&acc, component);
            }
            return acc;
        }

        match (expr, factor) {
            (Expression::Number(Number::Integer(a)), Expression::Number(Number::Integer(b))) => {
                if !b.is_zero() && (a % b).is_zero() {
                    Expression::integer(a / b)
                } else {
                    expr.clone()
                }
            }

            (Expression::Symbol(s1), Expression::Symbol(s2)) if s1 == s2 => Expression::integer(1),

            // `xⁿ ÷ x = xⁿ⁻¹` and `xⁿ ÷ xᵐ = xⁿ⁻ᵐ` (same base). WITHOUT this arm a
            // power falls through to `_ => expr.clone()` unchanged, so a common
            // monomial factor mis-divides — e.g. `factor(x² − x)` would wrongly
            // return `x·(x² − 1)` instead of `x·(x − 1)`. `Expression::pow`
            // canonicalises the result (`xⁿ⁻ᵐ` with the exponent `0 → 1`, `1 → x`).
            (Expression::Pow(base, exp), _) => {
                let Expression::Number(Number::Integer(n)) = exp.as_ref() else {
                    return expr.clone();
                };
                // The exponent being divided out: `1` for the bare base, `m` for `baseᵐ`.
                let out = match factor {
                    f if base.as_ref() == f => 1,
                    Expression::Pow(fbase, fexp) if fbase == base => {
                        match fexp.as_ref() {
                            Expression::Number(Number::Integer(m)) => *m,
                            _ => return expr.clone(),
                        }
                    }
                    _ => return expr.clone(),
                };
                if out <= 0 || out > *n {
                    return expr.clone(); // not a clean divisor ⇒ leave untouched
                }
                Expression::pow((**base).clone(), Expression::integer(n - out))
            }

            (Expression::Mul(factors), _) => {
                let mut remaining_factors = factors.as_ref().clone();
                if let Some(pos) = remaining_factors.iter().position(|f| f == factor) {
                    // An exact factor element ⇒ drop it.
                    remaining_factors.remove(pos);
                } else if let Some(pos) =
                    remaining_factors.iter().position(|f| power_of_same_base(f, factor))
                {
                    // A power-of-the-factor element (e.g. `x²` when dividing by `x`)
                    // ⇒ reduce it in place via the `Pow` arm above.
                    remaining_factors[pos] =
                        self.divide_by_factor(&remaining_factors[pos], factor);
                } else {
                    return expr.clone();
                }
                match remaining_factors.len() {
                    0 => Expression::integer(1),
                    1 => remaining_factors[0].clone(),
                    _ => Expression::mul(remaining_factors),
                }
            }

            _ => expr.clone(),
        }
    }

    /// Factor out numeric coefficients
    pub fn factor_numeric_coefficient(&self) -> (BigInt, Expression) {
        match self {
            Expression::Number(Number::Integer(n)) => (BigInt::from(*n), Expression::integer(1)),
            Expression::Number(Number::BigInteger(n)) => {
                (n.as_ref().clone(), Expression::integer(1))
            }
            Expression::Mul(factors) => {
                let mut coefficient = BigInt::one();
                let mut non_numeric_factors = Vec::new();

                for factor in factors.iter() {
                    match factor {
                        Expression::Number(Number::Integer(n)) => {
                            coefficient *= BigInt::from(*n);
                        }
                        Expression::Number(Number::BigInteger(n)) => {
                            coefficient *= n.as_ref();
                        }
                        _ => {
                            non_numeric_factors.push(factor.clone());
                        }
                    }
                }

                let remaining = if non_numeric_factors.is_empty() {
                    Expression::integer(1)
                } else if non_numeric_factors.len() == 1 {
                    non_numeric_factors[0].clone()
                } else {
                    Expression::mul(non_numeric_factors)
                };

                (coefficient, remaining)
            }
            _ => (BigInt::one(), self.clone()),
        }
    }
}

/// Is `candidate` a power `baseᵏ` divisible by `factor` — i.e. a `Pow` whose base
/// is the thing `factor` divides (`factor` itself a `Symbol`/`Pow` of that base)?
/// Used by `divide_by_factor` to spot a `Mul` element like `x²` that a divisor `x`
/// (or `x²`) reduces rather than removing outright.
fn power_of_same_base(candidate: &Expression, factor: &Expression) -> bool {
    let Expression::Pow(cbase, _) = candidate else {
        return false;
    };
    match factor {
        Expression::Pow(fbase, _) => fbase == cbase,
        other => cbase.as_ref() == other,
    }
}
