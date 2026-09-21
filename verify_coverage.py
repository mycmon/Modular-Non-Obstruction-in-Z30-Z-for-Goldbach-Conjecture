import time

def sieve_of_eratosthenes(limit):
    """Generates a boolean prime sieve up to limit."""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(limit**0.5) + 1):
        if is_prime[p]:
            for i in range(p * p, limit + 1, p):
                is_prime[i] = False
    return is_prime

def verify_full_triad_coverage(max_even=1_000_000):
    print("=" * 88)
    print(" GOLDBACH COVERAGE VERIFICATION WITH P30 = {1, 7, 11, 13, 17, 19, 23, 29} ")
    print("=" * 88)

    t0 = time.time()
    is_prime = sieve_of_eratosthenes(max_even)
    P30 = {1, 7, 11, 13, 17, 19, 23, 29}
    
    total_evens = 0
    covered_evens = 0
    missed_by_class = {c: 0 for c in range(0, 30, 2)}
    missed_integers = []
    
    for target in range(6, max_even + 1, 2):
        total_evens += 1
        found = False
        
        for p1 in range(7, target // 2 + 1, 2):
            if is_prime[p1] and (p1 % 30 in P30):
                p2 = target - p1
                if is_prime[p2] and (p2 % 30 in P30):
                    found = True
                    break
       
        if found:
            covered_evens += 1
        else:
            missed_integers.append(target)
            missed_by_class[target % 30] += 1

    t1 = time.time()

    print(f"\nExecution Summary for 2N <= {max_even:,}:")
    print(f"  Total evens tested        : {total_evens:,}")
    print(f"  Goldbach pairs found      : {covered_evens:,} ({covered_evens/total_evens*100:.4f}%)")
    print(f"  Execution time            : {t1 - t0:.2f}s")
    print(f"  Missed evens list         : {missed_integers}")
    print(f"  Missed distribution (mod 30): {missed_by_class}")
    print("=" * 88)

if __name__ == "__main__":
    verify_full_triad_coverage(1_000_000)
