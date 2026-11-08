#!/usr/bin/env python3
"""Verify the committed C++ coefficient expressions as exact polynomials.

This reads, but never regenerates or modifies, mixed_nonshort_coefficients.hpp.
It checks every declared intermediate and the returned Horner polynomial
against the independent numerator construction in the blowup certificate.
No interval exclusion, numerical sampling, Lean, Lake or CI is performed.
"""
from pathlib import Path
import hashlib
import re
import sympy as s

directory = Path(__file__).resolve().parent
namespace = {}
construction = directory.joinpath(
    'mixed_nonshort_completion_blowup_certificate.py').read_text()
exec(construction.split('# The quadratic-log model')[0], namespace)
a, c, epsilon, l0, l1, l2 = (
    namespace[name] for name in ('a', 'c', 'e', 'l0', 'l1', 'l2'))
numerator = namespace['poly']
T = a + c

path = directory / 'mixed_nonshort_coefficients.hpp'
raw = path.read_bytes()
lines = [line.strip() for line in raw.decode().splitlines()
         if line.strip() and not line.lstrip().startswith('//')]
assert lines[0] == (
    'template<class T>T centered_polynomial_cancelled(const T&a,const T&c,'
    'const T&eps,const T&l0,const T&l1,const T&l2){')
assert lines[-1] == '}'

values = {'a': a, 'c': c, 'eps': epsilon,
          'l0': l0, 'l1': l1, 'l2': l2}
declarations = []
returned = None


def expression(text):
    # The C++ body is restricted to the same exact polynomial language
    # that this verifier parses: integers, known names, +,-,*,powi.
    # In particular C++ integer division is not reinterpreted as a rational.
    assert re.fullmatch(r'[A-Za-z0-9_\s+*(),-]+', text), text
    assert '**' not in text
    names = set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*', text))
    assert names <= values.keys() | {'powi'}, names - values.keys()

    def power(base, exponent):
        exponent = s.sympify(exponent)
        assert exponent.is_Integer and 0 <= exponent <= 2**32 - 1
        return base ** exponent

    return s.expand(s.sympify(text, locals={
        **values, 'powi': power}))


for line in lines[1:-1]:
    match = re.fullmatch(r'const T (cx[0-9]+|C[2-8])=(.+);', line)
    if match:
        assert returned is None
        name, rhs = match.groups()
        assert name not in values
        values[name] = expression(rhs)
        declarations.append(name)
    else:
        match = re.fullmatch(r'return (.+);', line)
        assert match and returned is None, line
        returned = expression(match.group(1))

assert returned is not None
assert [name for name in declarations if name.startswith('cx')] == [
    'cx' + str(i) for i in range(53)]
assert [name for name in declarations if name.startswith('C')] == [
    'C' + str(i) for i in range(2, 9)]

for degree in range(2, 9):
    coefficient = values['C' + str(degree)]
    assert s.expand(coefficient * T**3 - numerator.nth(degree)) == 0
    print('PASS committed C++ coefficient C' + str(degree),
          'equals the exact numerator coefficient divided by (a+c)^3')

expected = sum(values['C' + str(i)] * epsilon**(i - 2)
               for i in range(2, 9))
assert s.expand(returned - expected) == 0
print('PASS committed Horner return equals all seven exact coefficients')
print('PASS 53 ordered intermediates and 7 output coefficients; no source mutation')
print('Header SHA256:', hashlib.sha256(raw).hexdigest())
