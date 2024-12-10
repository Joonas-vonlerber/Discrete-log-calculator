from math import sqrt, ceil, gcd, lcm
import primefac
from functools import reduce
from typing import TypeVar, Iterable
from random import randint

def is_in_mult_group(elem: int, modulo: int) -> bool:
    ' ' ' check that integer `elem` is in the multiplicative group of integers modulo `modulo` e.g. (Z_`modulo`)* ' ' '
    return 0 < elem < modulo and gcd(elem, modulo) == 1

T = TypeVar('T')
def count_freq(input: list[T]) -> list[tuple[T, int]]:
    '''
    Axillary function to calculate frequencies of elements in list.

    >>> count_freq([0,0,0,1,1,1,2,1])
    [(0, 3), (1, 4), (2, 1)]
    >>> count_freq([2,0,0,0,0,2,1])
    [(2, 2), (0, 4), (1, 1)]

    Args:
        input (list[T]): list of elements.
    
    Returns:
        frequencies: list of frequencies of elements.
    '''
    encountered = []
    freqs = []
    for c in input:
        if c in encountered:
            continue
        encountered.append(c)
        freq = input.count(c)
        freqs.append((c, freq))
    return freqs

def get_factors(n: int) -> list[tuple[int, int]]:
    '''
    Get factors of `n` in the form `[(p1, e1), (p2, e2)...]` for which `n = p1**e1 * p2**e2 * ...`

    >>> get_factors(3)
    [(3, 1)]
    >>> get_factors(3*5*5*5)
    [(3, 1), (5, 3)]
    '''
    factors = count_freq(list(primefac.primefac(n)))
    return sorted(factors, key=lambda t: t[0])


def get_random_elem_in_mult_group(modulo: int) -> int:
    '''
    Get a random element in the multiplicative group of integers modulo `modulo`

    >>> is_in_mult_group(get_random_elem_in_mult_group(200), 200)
    True
    >>> is_in_mult_group(get_random_elem_in_mult_group(1337), 1337)
    True
    ''' 
    a = 1
    b = modulo - 1
    guess = randint(a,b)
    while not gcd(guess,  modulo) == 1:
        guess = randint(a, b)
    return guess

def euler_phi(n: int, factors: list[tuple[int, int]] | None = None) -> int:
    '''
    Calculate the euler totient function of `n`. Function uses the factorization of `n` and if one has already computed them, one can input them to the optional argument `factors`.

    >>> euler_phi(5)
    4
    >>> euler_phi(2**64)
    9223372036854775808
    '''
    if factors == None:
        factors = get_factors(n)
    assert reduce(lambda a, b: a * pow(b[0], b[1]), factors, 1) == n
    return reduce(lambda a, b: a * (pow(b[0], b[1]) - pow(b[0], b[1]-1)), factors, 1) 

def carmichael_lambda(n: int, factors: list[tuple[int, int]] | None = None) -> int:
    '''
    Calculates the carmichael lambda function of `n`. Function uses the factorization of `n` and if one has already computed them, one can input them to the optional argument `factors`. 

    >>> carmichael_lambda(33)
    10
    >>> carmichael_lambda(16)
    4
    >>> carmichael_lambda(17)
    16
    '''
    if factors == None:
        factors = get_factors(n)
    
    # Carmichael lambda recurrence relation
    if n in [1,2,4] or (len(factors) == 1 and not factors[0][0] == 2):
        return euler_phi(n)
    elif len(factors) == 1 and factors[0][0] == 2:
        return 2**(factors[0][1] - 2)
    else:
        return lcm(*list(map(lambda x: carmichael_lambda(pow(x[0], x[1])), factors)))
    

def egcd(a: int,b: int) -> tuple[int, int, int]:
    '''
    The extended euclidian algorithm which calculates the `x`, `y` and `gcd(a,b)` in equation `ax+by=gcd(a,b)`.
    
    >>> egcd(240, 46)
    (2, -9, 47)
    '''
    if b == 0:
        return (a, 1, 0)
    else:
        q = a // b
        r = a % b
        d, x, y = egcd(b, r)
        return d, y, x-q*y

def mult_order_element(a: int, modulo: int) -> int:
    '''
    Calculates the order of `a` in Z_`modulo` by "trial multiplication" aka. multiply an a by a until it is 1 and count how many times we multiplied.

    >>> mult_order_element(8, 7**4)
    343
    >>> mult_order_element(4, 15)
    2
    '''
    assert is_in_mult_group(a, modulo)
    order = 1 # as a**1 = a so we don't check it.
    elem = a
    while not elem == 1:
        order += 1
        elem = (elem * a) % modulo
    return order

def modulo_has_primitive_root(n: int, factors: list[tuple[int, int]] | None = None) -> bool:
    '''
    Checks if a modulus `n` has a primitive root. This is true only when `n in [1,2,4,p**k, 2*p**k]` where `p in odd_primes`

    >>> modulo_has_primitive_root(1)
    True
    >>> modulo_has_primitive_root(2**4)
    False
    >>> modulo_has_primitive_root(3**5)
    True
    >>> modulo_has_primitive_root(2*7**5)
    True
    >>> modulo_has_primitive_root(3*7**5)
    False
    '''
    if factors == None:
        factors = get_factors(n)
    is_small = n in [1,2,4]
    is_odd_prime_power = len(factors) == 1 and not factors[0][0] == 2
    is_two_times_odd_prime_power = len(factors) == 2 and factors[0][0] == 2
    return is_small or is_odd_prime_power or is_two_times_odd_prime_power

def is_primitive_mod_n(a: int, n: int, factors: list[tuple[int, int]] | None = None, euler_phi_factors: list[tuple[int, int]] | None = None) -> bool:
    '''
    Checks if `a` is a primitive root modulo `n`. This is equivalent of saying that the order of `a` is the order of the group aka `euler_phi(n)`. This can only be true when `n in [1,2,4,p**k, 2*p**k]` where `p in odd_primes`. 

    >>> is_primitive_mod_n(3, 14)
    True
    >>> is_primitive_mod_n(3, 2**4)
    False
    >>> is_primitive_mod_n(11, 2*3**7)
    True
    '''
    assert is_in_mult_group(a,n)
    if factors == None:
        factors = get_factors(n)
    if not modulo_has_primitive_root(n, factors):
        return False
    factors_modulo = factors
    order = euler_phi(n, factors_modulo)
    if euler_phi_factors == None:
        euler_phi_factors = get_factors(order)
    factors_order = euler_phi_factors

    for (p, _) in factors_order:
        if pow(a, order // p, n) == 1:
            return False
    return True

def is_lambda_primitive_mod_n(a: int, n: int, factors: list[tuple[int, int]] | None = None, carmichael_factors: list[tuple[int, int]] | None = None) -> bool:
    '''
    Checks whether `a` is a primitive lambda root modulo `n` aka. `a` has order `carmichael_lambda(n).

    >>> is_lambda_primitive_mod_n(3, 14)
    True
    >>> is_lambda_primitive_mod_n(5, 1807)
    True
    >>> is_lambda_primitive_mod_n(4, 1807)
    False
    '''
    
    assert is_in_mult_group(a, n)
    if factors == None:
        factors = get_factors(n)
    biggest_order = carmichael_lambda(n, factors)
    if carmichael_factors == None:
        carmichael_factors = get_factors(biggest_order)
    
    for (p, _) in carmichael_factors:
        if pow(a, biggest_order // p, n) == 1:
            return False
    return True
    


def baby_step_giant_step(input: int, generator: int, modulo: int, order: int) -> int:
    '''
    Implementation of baby step giant step algorithm to calculate discrete log in time and space complexity `O(order)`.

    Args:

        input (int): number we want to calculate the discrete log of
        generator (int): the base of the logarithm, order of `generator` must be `order`
        modulo (int): the number defining the multiplicative group of integers modulo `modulo`
        order (int): order of generator

    Returns:
        dlog (int): the discrete log aka. the solution to the equation `g**x = input % modulo`


    >>> baby_step_giant_step(pow(7, 19, 23), 7, 23, 22)
    19
    '''
    if order == None:
        order = euler_phi(modulo)
    m = ceil(sqrt(order))
    generator_powers = { pow(generator, j, modulo):j for j in range(m) }
    gen_minus_m = pow(generator, -m, modulo)
    y = input
    for i in range(m):
        j = generator_powers.get(y)
        if j == None:
            y = (y * gen_minus_m) % modulo
        else:
            result = i * m + j
            return result

dlog = 19
p = 23
order = euler_phi(p)
generator = 7
input = pow(generator, dlog, p)

assert baby_step_giant_step(input, generator, p, p-1) == dlog


def pohlig_hellman_pk(input: int, generator: int, modulo: int, p: int, k: int) -> int:
    '''
    Calculates the discrete logarithm of input aka. calculates x in generator**x = input mod modulo when the order of the group is some prime p raised to the power of some k.

    Args:
        `input` (int): number we want to calculate the discrete log of
        `generator` (int): the base of the logarithm, order of generator must be p**k
        `modulo` (int): the n defining the base ring Z_n
        `p` (int): prime and the base of the order of generator
        `k` (int): the exponent of the order of generator
    
    Returns:
        `x` (int): the discrete logarithm of input
    
    >>> pohlig_hellman_pk(pow(8, 18, 7**4), 8, 7**4, 7, 3)
    18
    ''' 

    x = 0
    gamma = pow(generator, p**(k-1), modulo)
    h = None
    d = None
    for i in range(k):
        h = pow(pow(generator, -x, modulo) * input, p**(k-1-i), modulo)
        d = baby_step_giant_step(h, gamma, modulo, p)
        x = (x + d * p**i)
    return x


def crt_two_congruences(cong1: tuple[int, int], cong2: tuple[int, int]) -> int:
    '''
    Calculates the solution to a pair of congruence relations of the form x = a1 mod n1, x = a2 mod n2. n1 and n2 must be coprime. The calculation is done using 

    Args:
        `cong1` ((int, int)): First congruence (a1, n1) of the form x = a1 mod n1
        `cong2` ((int, int)): Second congruence (a2, n2) of the form x = a2 mod n2  
    
    Returns:
        `x` (int): the solution x to the congruence pair

    >>> crt_two_congruences((11,21), (7,13))
    137
    '''
    (a1, n1) = cong1
    (a2, n2) = cong2 
    d, m1, m2 = egcd(n1, n2)
    assert d == 1
    return (a1 * m2 * n2 + a2 * m1 * n1) % (n1*n2)
    


def chinese_remainder_theorem(congruences: Iterable[tuple[int, int]]) -> int:
    '''
    Calculates the solution x to the system of congruence relations of form `x = a mod n`. where `n`:s are coprime.

    Args:
        `congruences` ([(int, int)]): system of congruences `[(a1, n1), (a2, n2),...]`, where `ni` are coprime

    Returns:
        `x` (int): the solution x to the congruence system
    
    >>> chinese_remainder_theorem([(1, 2), (2, 3), (2, 5), (6, 7)])
    167
    '''
    def next_cong(cong1: tuple[int, int], cong2: tuple[int, int]) -> tuple[int, int]:
        (_, n1) = cong1
        (_, n2) = cong2
        return (crt_two_congruences(cong1, cong2), n1*n2)
    (x, _) = reduce(next_cong, congruences)
    return x


def pohlig_hellman(input: int, generator: int, modulo: int, order: int, prime_factorization: list[tuple[int, int]]| None = None) -> int:
    '''
    The silver-pohlig-hellman algorithm for calculating discrete logs of cyclic groups of order `order` generated by `generator` aka. calculates the solution `x` to the equation `generator**x = input mod modulo`.

    Args:

        `input` (int): number we want to calculate the discrete log of
        `generator` (int): the base of the logarithm and the generator of the cyclic group. Order of `generator` is `order`.
        `modulo` (int): the modulus defining the multiplicative group we work in aka. (Z_`modulo`)*
        `order` (int): the order of `generator`
        `prime_factorization` (optional, [(int, int)]): the prime_factorization of `order`. If one already knows the prime factorization, one can input them to this optional argument.

    >>> pohlig_hellman(pow(8, 18, 7**4), 8, 7**4, 7**3 ,[(7, 3)])
    18
    >>> pohlig_hellman(pow(5, 30, 1807), 5, 1807, 276)
    30
    '''
    
    if prime_factorization == None:
        prime_factorization = get_factors(order)
    # The round generator, round dlog arg and round dlog, placeholder values
    gi: int = 0
    hi: int = 0
    xi: int = 0
    prime_solutions: list[tuple[int, tuple[int, int]]] = []
    for (p, e) in prime_factorization:
        gi = pow(generator, order // (p**e), modulo)
        hi = pow(input, order // (p**e), modulo)
        xi = pohlig_hellman_pk(hi, gi, modulo, p, e)
        prime_solutions.append((xi, (p, e)))
    cong: map[tuple[int, int]] = map(lambda t: (t[0], pow(t[1][0], t[1][1])), prime_solutions)
    return chinese_remainder_theorem(cong)

if __name__ == "__main__":
    import doctest
    doctest.testmod()