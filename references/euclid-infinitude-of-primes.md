# Euchlid's proof of infinitely many primes

def: A natural number p is prime if p | a * b => p | a or p | b

def: A natural number p is irreduicble if p = a * b => p = a or p = b

def: if a b are naturals, the greatest common divisor gcd(a,b) = d is such that
- d | a
- d | b
- if c | a and c | b then c | d

lemma: if a b are naturals, there exists x,y integers such that x*a + y * b = gcd(a,b)
proof: TODO

lemma: A natural number p is irreducible iff its prime
proof:
Suppose p is prime, and p = a * b. Then p | a * b, so p | a or p | b.
If p | a then p * k = a => p = (p * k) * b => 1 = k * b => b = 1 => a = p.
A similar argument holds for p | b. Hence p is irreducible

Suppose p is irreduciple, and p | a * b, but not p | a. Let d = gcd(a,p). then p = k * d, so d = 1 or d = p.
if d = p, then a = k * p => p | a, contradiciton. So p | b

so d = 1, Then exists integers x,y with x * p + y * a = 1 => x * p * b + y * a * b = b. As p divides both summands on the lhs,
it divides the sum. Thus p | b.

lemma: let a,b be distinct natural numbers greater than 1. If a | b => a < b
proof: if a | b => exists a c with b = a * c. Since a b distinct, c > 1. Then
b - a = a * c - a = a * (c - 1) > 0 => b - a > 0 => b > a

theroem: For any natural number n > 1, there exists (p_1, e_1), ... (p_k, e_k) with p_i distict primes and e_i > 0 forall i
such that n = \Product_{1}^{k} p_i ^ e_i
proof: induction on n
base case: n = 2, immediate
induction case, suppose true for 2 ... n 
If n + 1 is prime, then were done. Otherwise n + 1 is irreducible, so (n + 1) = a * b with niether a nor b eqaual to 1. 
Then a < n + 1 and b < n + 1, so we can apply the induction hypothesis to both a and b. Combine their factorizations to get the result.


## Note: I dont think we actually need this uniqueness
theroem: for any natrual number n > 1, given a prime factorization n = \Product_{1}^{k} p_p ^ e_i, it is unique up to ordering.
proof. Let n = \Product_{1}^{k} p_i ^ e_i  = \Product_{1}^{l} q_j ^ f_j be two factorizations. Then forall i, p_i | RHS => p_i | q_j^f_j
some j => p_i = q_j some j. Similarly forall j, there exists a unique i such that q_j = p_i. This establishes a bijection [k] -> [l], {p_i} -> {q_j}. 
Tmeans you can rewrite

  n = \Product_{1}^{k} p_i ^ e_i = \Product_{2}^{k} p_i ^ f_i


suupose exists and i with f_i > e_i. Up to reordering, suppose its i=1. Then
  
  n = \Product_{2}^{k} p_i ^ e_i  = p_i^(f_1 - e_1) * \Product_{2}^{k} p_i ^ f_i

meaning p | RHS but not the left, contradction. Similar if ei > fi for some i. Thus ei = fi for all i, hence the result.


corollary: For any natural number n > 1, there exists unique (p_1, e_1), ... (p_k, e_k) with p_i distict primes and e_i > 0 forall i
such that n = \Product_{1}^{k} p_i ^ e_i


theorem: There are inifinitely many primes.

Suppose there are only finitely many primes p1...pn. let m = (\prod_{i=1}^{n} p_i). Then n admits a prime factorization

  m + 1 = \Product_{j=1}^{k} p_j ^ e_j

. Then for all p_j, p_j | m + 1, p_j | m => m_j | 1, contradiction. 

