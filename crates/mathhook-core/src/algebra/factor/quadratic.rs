//! Quadratic factoring and special patterns

use crate::core::{Expression, Number, Symbol};

impl Expression {
    /// Try to factor a single-variable integer quadratic `a·v² + b·v + c` into
    /// linear factors over ℤ (difference of squares, monic, or general via the
    /// discriminant). Returns `None` when the terms are not such a quadratic, when
    /// the discriminant is negative or not a perfect square (⇒ no rational linear
    /// factors), or when the constructed factorization fails its arithmetic
    /// re-check — so a mis-parse can only decline, never emit a wrong factorization.
    pub(super) fn try_quadratic_factoring(&self, terms: &[Expression]) -> Option<Expression> {
        let (var, a, b, c) = parse_integer_quadratic(terms)?;

        // Discriminant b² − 4ac (i128 to soften overflow; huge inputs decline).
        let disc = b.checked_mul(b)?.checked_sub(4i128.checked_mul(a)?.checked_mul(c)?)?;
        if disc < 0 {
            return None; // no real roots ⇒ irreducible over ℝ
        }
        let root = isqrt(disc);
        if root.checked_mul(root)? != disc {
            return None; // irrational roots ⇒ does not factor over ℚ
        }

        // Roots (−b ± root) / (2a) reduced to lowest terms (num/den, den > 0). The
        // linear factor for a root n/d is `d·v − n` (leading = d, constant = −n).
        let two_a = 2i128.checked_mul(a)?;
        let (n1, d1) = reduced_fraction(-b + root, two_a)?;
        let (n2, d2) = reduced_fraction(-b - root, two_a)?;
        let (l1, e1) = (d1, -n1); // factor 1: l1·v + e1
        let (l2, e2) = (d2, -n2); // factor 2: l2·v + e2

        // Content k so that k·(l1·v + e1)·(l2·v + e2) = a·v² + b·v + c. The product's
        // leading coefficient is l1·l2, so k = a / (l1·l2) must be an exact integer.
        let ll = l1.checked_mul(l2)?;
        if ll == 0 || a % ll != 0 {
            return None;
        }
        let k = a / ll;

        // ARITHMETIC RE-CHECK (order-independent, no symbolic expansion): the
        // expanded coefficients of k·(l1·v + e1)(l2·v + e2) must equal (a, b, c).
        let a_chk = k.checked_mul(ll)?;
        let b_chk = k.checked_mul(l1.checked_mul(e2)?.checked_add(l2.checked_mul(e1)?)?)?;
        let c_chk = k.checked_mul(e1.checked_mul(e2)?)?;
        if (a_chk, b_chk, c_chk) != (a, b, c) {
            return None;
        }

        let f1 = build_linear(&var, l1, e1)?;
        let f2 = build_linear(&var, l2, e2)?;
        let product = if k == 1 {
            Expression::mul(vec![f1, f2])
        } else {
            Expression::mul(vec![int_expr(k)?, f1, f2])
        };
        Some(product)
    }

    /// Factor perfect square trinomials: a^2 + 2ab + b^2 = (a + b)^2
    pub fn factor_perfect_square(&self, terms: &[Expression]) -> Option<Expression> {
        if terms.len() != 3 {
            return None;
        }

        None
    }

    /// Factor difference of squares: a^2 - b^2 = (a + b)(a - b)
    pub fn factor_difference_of_squares(&self, a: &Expression, b: &Expression) -> Expression {
        Expression::mul(vec![
            Expression::add(vec![a.clone(), b.clone()]),
            Expression::add(vec![
                a.clone(),
                Expression::mul(vec![Expression::integer(-1), b.clone()]),
            ]),
        ])
    }
}

/// Parse the terms of an `Add` into a single-variable integer quadratic
/// `a·v² + b·v + c`, returning `(var, a, b, c)` with `a ≠ 0`. Declines (`None`) on
/// anything that is not exactly a degree-2 univariate integer polynomial (a second
/// variable, a non-integer coefficient, a degree > 2, an i64-overflowing literal).
fn parse_integer_quadratic(terms: &[Expression]) -> Option<(Symbol, i128, i128, i128)> {
    let mut coeffs = [0i128; 3]; // [c0, c1, c2]
    let mut var: Option<Symbol> = None;

    for term in terms {
        let (deg, coeff, term_var) = parse_monomial(term)?;
        if deg > 2 {
            return None;
        }
        if let Some(v) = term_var {
            match &var {
                Some(existing) if existing != &v => return None, // multivariate
                _ => var = Some(v),
            }
        }
        coeffs[deg] = coeffs[deg].checked_add(coeff)?;
    }

    let var = var?; // a pure constant is not a quadratic
    if coeffs[2] == 0 {
        return None; // degree < 2 ⇒ not a quadratic
    }
    Some((var, coeffs[2], coeffs[1], coeffs[0]))
}

/// Parse one term into `(degree, integer coefficient, variable)`. The variable is
/// `None` for a constant term. Declines on any non-monomial shape.
fn parse_monomial(term: &Expression) -> Option<(usize, i128, Option<Symbol>)> {
    match term {
        Expression::Number(n) => Some((0, number_to_i128(n)?, None)),
        Expression::Symbol(s) => Some((1, 1, Some(s.clone()))),
        Expression::Pow(base, exp) => {
            let Expression::Symbol(s) = base.as_ref() else {
                return None;
            };
            let Expression::Number(Number::Integer(k)) = exp.as_ref() else {
                return None;
            };
            let k = usize::try_from(*k).ok()?;
            Some((k, 1, Some(s.clone())))
        }
        Expression::Mul(factors) => {
            let mut coeff: i128 = 1;
            let mut deg: usize = 0;
            let mut var: Option<Symbol> = None;
            for f in factors.iter() {
                match f {
                    Expression::Number(n) => coeff = coeff.checked_mul(number_to_i128(n)?)?,
                    Expression::Symbol(s) => {
                        if var.as_ref().is_some_and(|v| v != s) {
                            return None; // two distinct variables in one term
                        }
                        var = Some(s.clone());
                        deg = deg.checked_add(1)?;
                    }
                    Expression::Pow(base, exp) => {
                        let Expression::Symbol(s) = base.as_ref() else {
                            return None;
                        };
                        let Expression::Number(Number::Integer(k)) = exp.as_ref() else {
                            return None;
                        };
                        if var.as_ref().is_some_and(|v| v != s) {
                            return None;
                        }
                        var = Some(s.clone());
                        deg = deg.checked_add(usize::try_from(*k).ok()?)?;
                    }
                    _ => return None,
                }
            }
            Some((deg, coeff, var))
        }
        _ => None,
    }
}

fn number_to_i128(n: &Number) -> Option<i128> {
    match n {
        Number::Integer(i) => Some(*i as i128),
        Number::BigInteger(b) => i128::try_from(b.as_ref().clone()).ok(),
        _ => None, // Float / Rational ⇒ not an integer coefficient
    }
}

/// Non-negative integer square root of `n ≥ 0` (floor).
fn isqrt(n: i128) -> i128 {
    if n < 2 {
        return n;
    }
    let mut x = n;
    let mut y = (x + 1) / 2;
    while y < x {
        x = y;
        y = (x + n / x) / 2;
    }
    x
}

/// Reduce `num/den` to lowest terms with a POSITIVE denominator; `None` if `den == 0`.
fn reduced_fraction(num: i128, den: i128) -> Option<(i128, i128)> {
    if den == 0 {
        return None;
    }
    let g = num_integer::gcd(num.abs(), den.abs()).max(1);
    let (mut n, mut d) = (num / g, den / g);
    if d < 0 {
        n = -n;
        d = -d;
    }
    Some((n, d))
}

fn int_expr(k: i128) -> Option<Expression> {
    i64::try_from(k).ok().map(Expression::integer)
}

/// Build the linear factor `l·v + e` (canonicalised by `mul`/`add`).
fn build_linear(var: &Symbol, l: i128, e: i128) -> Option<Expression> {
    let lead = Expression::mul(vec![int_expr(l)?, Expression::Symbol(var.clone())]);
    if e == 0 {
        Some(lead)
    } else {
        Some(Expression::add(vec![lead, int_expr(e)?]))
    }
}

#[cfg(test)]
mod tests {
    use crate::algebra::Expand;
    use crate::{symbol, Expression, Factor};

    /// `x^2 + b·x + c` as a canonical `Add`.
    fn quad(x: &crate::Symbol, b: i64, c: i64) -> Expression {
        let mut terms = vec![Expression::pow(
            Expression::symbol(x.clone()),
            Expression::integer(2),
        )];
        if b != 0 {
            terms.push(Expression::mul(vec![
                Expression::integer(b),
                Expression::symbol(x.clone()),
            ]));
        }
        if c != 0 {
            terms.push(Expression::integer(c));
        }
        Expression::add(terms)
    }

    /// A factored quadratic must (a) become a product and (b) expand back to the
    /// original — the strongest end-to-end check.
    fn assert_factors_back(original: Expression) {
        let factored = original.factor();
        assert!(
            matches!(factored, Expression::Mul(_)),
            "expected a product, got {factored}"
        );
        assert_eq!(
            factored.expand(),
            original,
            "expanded factorization must equal the original"
        );
    }

    #[test]
    fn difference_of_squares_factors_and_expands_back() {
        let x = symbol!(x);
        assert_factors_back(quad(&x, 0, -1)); // x² − 1 = (x−1)(x+1)
        assert_factors_back(quad(&x, 0, -9)); // x² − 9 = (x−3)(x+3)
    }

    #[test]
    fn monic_quadratic_with_integer_roots_factors_and_expands_back() {
        let x = symbol!(x);
        assert_factors_back(quad(&x, -3, 2)); // x² − 3x + 2 = (x−1)(x−2)
        assert_factors_back(quad(&x, 5, 6)); //  x² + 5x + 6 = (x+2)(x+3)
    }

    #[test]
    fn irreducible_quadratic_is_left_unfactored() {
        let x = symbol!(x);
        // x² + 1 has a negative discriminant ⇒ no rational factors; factor() must
        // return it unchanged (not a bogus product).
        let p = quad(&x, 0, 1);
        assert_eq!(p.clone().factor(), p);
        // x² + x + 1 (discriminant −3, not a perfect square) likewise.
        let q = quad(&x, 1, 1);
        assert_eq!(q.clone().factor(), q);
    }

    #[test]
    fn multivariate_is_not_mistaken_for_a_quadratic() {
        let x = symbol!(x);
        let y = symbol!(y);
        // x² + y: a second variable ⇒ the quadratic parser declines, no factoring.
        let p = Expression::add(vec![
            Expression::pow(Expression::symbol(x), Expression::integer(2)),
            Expression::symbol(y),
        ]);
        assert_eq!(p.clone().factor(), p);
    }
}
