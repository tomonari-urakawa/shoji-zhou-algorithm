using Pkg
# if necessary
# Pkg.add("Nemo")
# Pkg.add("Combinatorics")
# Pkg.add("Oscar")

using Nemo
using Combinatorics
using LinearAlgebra
#using Oscar

# This is a Julia implementation of the algorithm described in the following paper:
# [SZ]  T.Shoji, Z.Zhou; Algorithm for computing canonical bases and foldings of quantum groups
# https://arxiv.org/abs/2506.00793

# ==========================================
# 1. Input
# ==========================================
# reduced words in paper [SZ]
# A_2n-1 : [1, 2n-1, 3, 2n-3,...,2, 2n-2, 4, 2n-4,......, 1, 2n-1, 3, 2n-3,...,2, 2n-2, 4, 2n-4,...] : n-times
# B_n, C_n : [1, 3, 5,...,2, 4, 6,...,1, 3, 5,...2, 4, 6,......] : n-times
# D_4 : [1, 3, 4, 2, 1, 3, 4, 2, 1, 3, 4, 2]
# D_2n-1 : [1, 3,..., n, n-1, 2, 4,...,......., 1, 3,..., n, n-1, 2, 4,...,] : (2n-2)-times
# D_2n : [1, 3,..., 2, 4,...n, n-1,......., 1, 3,..., 2, 4,..., n, n-1] : (2n-1)-times
# E_6 : [1, 6, 3, 5, 4, 2,...,1, 6, 3, 5, 4, 2] : 6-times
# F_4 : [1, 3, 2, 4, 1, 3, 2, 4, 1, 3, 2, 4, 1, 3, 2, 4, 1, 3, 2, 4, 1, 3, 2, 4]
# G_2 : [1, 2, 1, 2, 1, 2]

Type_Input = ['G', 2]  
h_paper = [1, 2, 1, 2, 1, 2]
weight = [2,1]

# ==========================================
# 2. Setup Environment
# ==========================================
R_poly, q_poly = polynomial_ring(QQ, "q")
RF = fraction_field(R_poly)
q = gen(RF)

# ==========================================
# 3. Generic Cartan Matrix & Helper Functions
# ==========================================
# Cartan Matrix
function create_cartan_matrix(type_char::Char, rank::Int)
    # cartan_matrix = (2*(j,i) / (i,i))_ij
    M = zeros(Int, rank, rank)
    
    for i in 1:rank
        M[i, i] = 2
    end

    if type_char == 'A'
        for i in 1:rank-1
            M[i, i+1] = -1
            M[i+1, i] = -1
        end
    elseif type_char == 'B'
        for i in 1:rank-1
            M[i, i+1] = -1
            M[i+1, i] = -1
        end
        if rank > 1
            M[rank-1, rank] = -1
            M[rank, rank-1] = -2
        end
    elseif type_char == 'C'
        for i in 1:rank-1
            M[i, i+1] = -1
            M[i+1, i] = -1
        end
        if rank > 1
            M[rank-1, rank] = -2
            M[rank, rank-1] = -1
        end
    elseif type_char == 'D'
        for i in 1:rank-2
            M[i, i+1] = -1
            M[i+1, i] = -1
        end
        if rank >= 3
            M[rank-2, rank] = -1
            M[rank, rank-2] = -1
            M[rank-2, rank-1] = -1
            M[rank-1, rank-2] = -1
        end
    elseif type_char == 'G' && rank == 2
        # G2 dual
        M[1, 2] = -1
        M[2, 1] = -3
    elseif type_char == 'F' && rank == 4
        M[1,2] = -1; M[2,1] = -1
        M[2,3] = -1; M[3,2] = -2
        M[3,4] = -1; M[4,3] = -1
    elseif type_char == 'E'
        indices = 1:rank
        edges = []
        if rank >= 6
            push!(edges, (1,3), (3,4), (4,2), (4,5), (5,6))
        end
        if rank >= 7; push!(edges, (6,7)); end
        if rank >= 8; push!(edges, (7,8)); end
        
        for (u, v) in edges
            M[u,v] = -1; M[v,u] = -1
        end
    end
    return(M)
end

# Symmetrizer
function compute_symmetrizer(CM::Matrix{Int})
    n = size(CM, 1)
    
    d_rational = zeros(Rational{Int}, n)
    visited = zeros(Bool, n)
    
    start_node = 1
    d_rational[start_node] = 1 // 1
    visited[start_node] = true
    queue = [start_node]
    
    head = 1
    while head <= length(queue)
        u = queue[head]; head += 1
        
        for v in 1:n
            if CM[u, v] != 0 && !visited[v]
                # Symmetrization condition: d_v = d_u * (A_uv / A_vu)
                d_rational[v] = d_rational[u] * (CM[u, v] // CM[v, u])
                
                visited[v] = true
                push!(queue, v)
            end
        end
    end

    lcm_val = lcm(denominator.(d_rational)) # LCM of denominators for all elements

    return Int.(d_rational .* lcm_val)
end

function get_simple_roots_order(type_char::Char, rank::Int)# [SZ 4.3, 4.9]
    n = rank
    simple_roots_order = Int[]
    if type_char == 'A' && (n-1) % 2 == 0
        for i in range(1,(n+1)÷2,step=2)
            push!(simple_roots_order,i)
            if i < (n+1)÷2
                push!(simple_roots_order,n+1-i)
            end
        end
        if n >= 3
            for i in range(2,(n+1)÷2,step=2)
                push!(simple_roots_order,i)
                if i < (n+1)÷2
                    push!(simple_roots_order,n+1-i)
                end
            end
        end
    elseif type_char == 'B' || type_char == 'C'
        for i in range(1,n,step=2)
            push!(simple_roots_order,i)
        end
        for i in range(2,n,step=2)
            push!(simple_roots_order,i)
        end
    elseif type_char == 'D' && n == 4
        simple_roots_order = [1,3,4,2]
    elseif type_char == 'D' && n > 4 && (n-1) % 2 == 0
        for i in range(1,n,step=2)
            push!(simple_roots_order,i)
            if i == n
                push!(simple_roots_order,i-1)
            end
        end
        for i in range(2,n-2,step=2)
            push!(simple_roots_order,i)
        end
    elseif type_char == 'D' && n > 4 && n % 2 == 0
        for i in range(1,n-2,step=2)
            push!(simple_roots_order,i)
        end
        for i in range(2,n,step=2)
            push!(simple_roots_order,i)
            if i == n
                push!(simple_roots_order,i-1)
            end
        end
    elseif type_char == 'E' && n == 6
        simple_roots_order = [1,6,4,3,5,2]
    elseif type_char == 'F'
        simple_roots_order = [1,3,2,4]
    else #G2
        simple_roots_order = collect(1:n)
    end
    return(simple_roots_order)
end

function folding(type_char::Char, rank::Int) # [SZ 4.3]
    n = rank
    orbit = Dict{Int, Int}()
    for i in 1:n; orbit[i] = i; end

    if type_char == 'A'
        for i in 1:n
            orbit[i] = min(i, n + 1 - i)
        end
    elseif type_char == 'D' && n == 4
        orbit[1] = 1; orbit[3] = 1; orbit[4] = 1; orbit[2] = 2
    elseif type_char == 'D' && n > 4
        orbit[n] = n-1
        orbit[n-1] = n-1
    elseif type_char == 'E' && n == 6
        orbit[1] = 1; orbit[6] = 1
        orbit[3] = 3; orbit[5] = 3
    end
    return(orbit)
    println(orbit)
end

# Type of some variables
struct MonomialBasisSolver{T}
    Type::Char
    CM::Matrix{Int}
    n_roots::Int
    q::T
    D_diag::Vector{Int}
    inner_product_matrix::Matrix{Int}
    orbit::Dict{Int, Int}

    function MonomialBasisSolver(cartan_matrix::Matrix{Int}, q_var)
        type = Type_Input[1]
        n = size(cartan_matrix, 1)
        symmetrizer = compute_symmetrizer(cartan_matrix)
        D_mat = zeros(Int, n, n)
        for i in 1:n
            D_mat[i,i] = symmetrizer[i]
        end
        Inner = D_mat * cartan_matrix
        orbit = folding(Type_Input[1], n)

        new{typeof(q_var)}(type, cartan_matrix, n, q_var, symmetrizer, Inner, orbit)
    end
end

# --- fuctors ---

# q-integer
function q_int(solver::MonomialBasisSolver, n::Int, i::Int)
    d_i = solver.D_diag[i]
    q_val = solver.q
    q_i = q_val^d_i
    if n == 0; return one(RF); end
    return (q_i^n - q_i^(-n)) // (q_i - q_i^(-1))
end

# q-factorial
function q_factorial(solver::MonomialBasisSolver, n::Int, i::Int)
    res = one(RF)
    for k in 1:n; res *= q_int(solver, k, i); end
    return res
end

function delta_factor(solver::MonomialBasisSolver, sequence_generators::Vector{Tuple{Int, Int}})
    # [SZ 5.19]
    res = one(RF)
    for (idx, count) in sequence_generators
        d_i = solver.D_diag[idx]
        q_val = solver.q
        q_i = q_val^d_i
        res *= (1 - q_i^2)^count
    end
    return res
end

function expand_sequence(sequence_generators::Vector{Tuple{Int, Int}})
    #(index, count) --> [index, index,...]    
    expanded = Int[]
    for (idx, count) in sequence_generators
        append!(expanded, fill(idx, count))
    end
    return expanded
end

function get_valid_permutations(nu::Vector{Int}, nu_prime::Vector{Int}) 
    #[SZ 5.17]
    n = length(nu)
    if length(nu_prime) != n; return Vector{Int}[]; end

    pos_nu = Dict{Int, Vector{Int}}()
    pos_nu_prime = Dict{Int, Vector{Int}}()

    for (i, root) in enumerate(nu)
        if !haskey(pos_nu, root); pos_nu[root] = Int[]; end
        push!(pos_nu[root], i)
    end
    for (i, root) in enumerate(nu_prime)
        if !haskey(pos_nu_prime, root); pos_nu_prime[root] = Int[]; end
        push!(pos_nu_prime[root], i)
    end

    if keys(pos_nu) != keys(pos_nu_prime); return Vector{Int}[]; end
    for root in keys(pos_nu)
        if length(pos_nu[root]) != length(pos_nu_prime[root]); return Vector{Int}[]; end
    end

    sub_permutations = []
    roots_order = sort(collect(keys(pos_nu)))

    for root in roots_order
        src = pos_nu[root]
        dst = pos_nu_prime[root]
        perms = []
        for p in permutations(dst)
            mapping = Dict{Int, Int}()
            for (s, d) in zip(src, p); mapping[s] = d; end
            push!(perms, mapping)
        end
        push!(sub_permutations, perms)
    end

    valid_ws = Vector{Int}[]
    for combo in Iterators.product(sub_permutations...)
        full_mapping = Dict{Int, Int}()
        for m in combo; merge!(full_mapping, m); end
        w = zeros(Int, n)
        for k in 1:n; w[k] = full_mapping[k]; end
        push!(valid_ws, w)
    end
    return valid_ws
end

function compute_A_statistic(solver::MonomialBasisSolver, w::Vector{Int}, nu::Vector{Int})
    #[SZ 5.17]
    n = length(w)
    total_A = 0
    for k in 1:n
        for l in (k+1):n
            if w[k] > w[l]
                total_A += solver.inner_product_matrix[nu[k], nu[l]]
            end
        end
    end
    return total_A
end

function compute(solver::MonomialBasisSolver, monomial1::Vector{Tuple{Int, Int}}, monomial2::Vector{Tuple{Int, Int}})
    #[SZ 6.4]
    nu = expand_sequence(monomial1)
    nu_prime = expand_sequence(monomial2)
    if sort(nu) != sort(nu_prime); return zero(RF); end
    
    fact_term = one(RF)
    for (idx, count) in monomial1; fact_term *= q_factorial(solver, count, idx); end
    for (idx, count) in monomial2; fact_term *= q_factorial(solver, count, idx); end
    
    delta_val = delta_factor(solver, monomial1)
    prefactor = 1 // (fact_term * delta_val)
    #println(fact_term)
    #println(delta_val)
    
    sum_q_A = zero(RF)
    for w in get_valid_permutations(nu, nu_prime)
        A_val = compute_A_statistic(solver, w, nu)
        sum_q_A += solver.q^(-A_val)
    end
    #println("q^-A(xi)=$sum_q_A")
    
    return prefactor * sum_q_A, sum_q_A
end


# --- root system ---

# simple reflection
function simple_reflection(root_coeffs::Vector{Int}, i::Int, CM::Matrix{Int})
    new_coeffs = copy(root_coeffs)
    factor = 0
    for j in 1:length(root_coeffs)
        # beta = sum (c_j * alpha_j)
        # s_i(beta) = alpha_j - (sum (c_j * a_ij)) * alpha_i
        # factor = sum (c_j * a_ij)
        factor += root_coeffs[j] * CM[i, j]
    end
    new_coeffs[i] -= factor
    return new_coeffs
end

# positive roots from reduced word of longest element with total(convex) order
function get_positive_roots_from_h(solver::MonomialBasisSolver, h::Vector{Int})
    n = solver.n_roots
    betas = Vector{Vector{Int}}()
    
    # Standard basis for simple roots
    simple_roots = [zeros(Int, n) for _ in 1:n]
    for i in 1:n; simple_roots[i][i] = 1; end
    
    for k in 1:length(h)
        idx = h[k]
        beta = copy(simple_roots[idx])
        
        history = h[1:k-1]
        for ref_idx in reverse(history)
            beta = simple_reflection(beta, ref_idx, solver.CM)
        end
        push!(betas, beta)
    end
    println("Betas from h:")
    println(betas)
    return betas
end

# weight --> sum of positive roots 
# Σa_iα_i = Σc_iβ_i
function solve_partition(solver::MonomialBasisSolver, target_weight::Vector{Int}, betas::Vector{Vector{Int}}, index::Int=1)
    if index > length(betas)
        return all(x -> x == 0, target_weight) ? [Int[]] : Vector{Int}[]
    end

    current_beta = betas[index]
    res = Vector{Int}[]
    
    max_c = Inf
    for (t, b) in zip(target_weight, current_beta)
        if b > 0; max_c = min(max_c, floor(Int, t / b));
        elseif b == 0 && t < 0; return Vector{Int}[]; end
    end
    if max_c == Inf; max_c = 0; end
    
    for c_k in 0:Int(max_c)
        next_target = target_weight .- (c_k .* current_beta)
        for sub_c in solve_partition(solver, next_target, betas, index + 1)
            push!(res, vcat([c_k], sub_c))
        end
    end
    return res
end


function construct_monomial_from_c(solver::MonomialBasisSolver, c::Vector{Int}, betas::Vector{Vector{Int}}, reduced_word::Vector{Int})
    # [SZ 4.14, 4.17]
    simple_roots_order = get_simple_roots_order(solver.Type, solver.n_roots)
    multiplication_order = reverse(simple_roots_order)
    #println(multiplication_order)
    groups = Vector{Vector{Int}}()
    is_sym = (solver.CM == transpose(solver.CM))
    
    if reduced_word === nothing || !is_sym
        for k in 1:length(c); push!(groups, [k]); end
    else
        current_group = Int[]
        for k in 1:length(c)
            idx = reduced_word[k]
            if isempty(current_group); push!(current_group, k)
            else
                prev_idx = reduced_word[current_group[end]]
                if solver.orbit[idx] == solver.orbit[prev_idx]
                    push!(current_group, k)
                else
                    push!(groups, current_group)
                    current_group = [k]
                end
            end
        end
        if !isempty(current_group); push!(groups, current_group); end
        # push last current_group into groups
    end
    
    total_monomial = Tuple{Int, Int}[]
    for grp in groups
        d_k = Dict{Int, Int}()
        for k in grp
            val = c[k]
            if val == 0; continue; end
            for idx in 1:solver.n_roots
                d_k[idx] = get(d_k, idx, 0) + val * betas[k][idx]
            end
        end
        
        sub_monomial = Tuple{Int, Int}[]
        for idx in multiplication_order
            exponent = get(d_k, idx, 0)
            if exponent > 0; push!(sub_monomial, (idx, exponent)); end
        end
        append!(total_monomial, sub_monomial)
    end
    return total_monomial
end

# get matrix Lambda [SZ 1.9, 5.20]
function compute_all_inner_products(solver::MonomialBasisSolver, target_weight::Vector{Int}, reduced_word::Vector{Int})
    betas = get_positive_roots_from_h(solver, reduced_word)
    valid_cs = solve_partition(solver, target_weight, betas)
    sort!(valid_cs)
    println(sort!(valid_cs))
    
    monomials = [construct_monomial_from_c(solver, c, betas, reduced_word) for c in valid_cs]
    num_basis = length(monomials)
    println("Found $num_basis monomial bases for weight $target_weight")
    println(monomials)

    Lambda = Matrix{typeof(solver.q)}(undef, num_basis, num_basis)
    Qs = Matrix{typeof(solver.q)}(undef, num_basis, num_basis)
    # Qs = (Σq^-A(xi))
    for i in 1:num_basis
        for j in i:num_basis
            lambdas, qs = compute(solver, monomials[i], monomials[j])
            val = lambdas
            Lambda[i, j] = lambdas
            Lambda[j, i] = lambdas
            val = qs
            Qs[i, j] = qs
            Qs[j, i] = qs
        end
    end
    return Lambda, monomials, valid_cs, Qs
end


# --- Matrix Decomposition & Laurent Polynomials ---

L_poly, q_L = laurent_polynomial_ring(QQ, "q")

# LDL decomposition using Schur complement
function solve_reverse_ldl(L_in)
    n = size(L_in, 1)
    A, H, D = copy(L_in), identity_matrix(RF, n), zero_matrix(RF, n, n)
    
    for i in n:-1:1
        pivot = A[i, i]
        D[i, i] = pivot
        #println(pivot)
        for j in 1:i-1; H[i, j] = A[i, j] // pivot; end
        for r in 1:i-1, c in 1:i-1
            A[r, c] -= H[i, r] * H[i, c] * pivot
        end
    end
    return H, D
end

# get coefficients laurent polynomial 
function get_terms_iterator(laurent_poly)
    if iszero(laurent_poly)
        return []
    end

    base_poly = laurent_poly.poly
    shift = laurent_poly.mindeg

    return ((Nemo.coeff(base_poly, i), i + shift) for i in 0:degree(base_poly) if Nemo.coeff(base_poly, i) != 0)
end

# rational funtion --> laurent polynomial
function to_laurent(elem)
    num, den = numerator(elem), denominator(elem)
    p2l(p) = sum(Nemo.coeff(p, i) * q_L^i for i in 0:degree(p) if Nemo.coeff(p, i)!=0; init=zero(L_poly))
    return p2l(num) * inv(p2l(den))
end

# laurent polynomial --> (principal part) + (constant part) + (regular part)
function split_poly(poly)
    plus, minus, z = zero(L_poly), zero(L_poly), zero(L_poly)

    for (c, i) in get_terms_iterator(poly)
        t = c * q_L^i
        if i > 0
            plus += t
        elseif i < 0
            minus += t
        else
            z += t
        end
    end
    return plus, minus, z
end

# bar-involution q -> q^-1
function bar_involution(poly)
    return sum(c * q_L^(-i) for (c, i) in get_terms_iterator(poly); init=zero(L_poly))
end

# H --> PQ
function compute_canonical_transition_matrices(H_in)
    #[SZ 1.10]
    n = size(H_in, 1)
    P, Q = identity_matrix(L_poly, n), identity_matrix(L_poly, n)
    
    for i in 1:n
        for j in (i-1):-1:1
            sum_val = sum(P[i, k] * Q[k, j] for k in (j+1):(i-1); init=zero(L_poly))
            a = to_laurent(H_in[i, j]) - sum_val
            a_plus, a_minus, a_zero = split_poly(a)
            bar_a_minus = bar_involution(a_minus)
            P[i, j] = a_plus - bar_a_minus
            Q[i, j] = a_minus + a_zero + bar_a_minus
        end
    end
    return P, Q
end

# ==========================================
# 4. Execution
# ==========================================
cartan_matrix = create_cartan_matrix(Type_Input[1], Type_Input[2])
symmetrizer = compute_symmetrizer(cartan_matrix)
solver = MonomialBasisSolver(cartan_matrix, q);

println("Using Cartan Matrix:")
show(stdout, "text/plain", cartan_matrix); print("\n")

#println("Diagonal entries (d_i):")
#show(stdout, "text/plain", symmetrizer)

Lambda, monomials, cs, Qs = compute_all_inner_products(solver, weight, h_paper);
H, D = solve_reverse_ldl(Lambda);
P_mat, Q_mat = compute_canonical_transition_matrices(H);

#println("Computed Matrix q-sum:")
#show(stdout, "text/plain", Qs); print("\n")

println("Computed Matrix Lambda:")
show(stdout, "text/plain", Lambda); print("\n")

println(" H (PBW -> Mon):")
show(stdout, "text/plain", H); print("\n")

println("D (InnerProdofPBW):")
show(stdout, "text/plain", D); print("\n")

println("P:PBW -> Can (off-diagonals in qZ[q])=")
show(stdout, "text/plain", P_mat); print("\n")

println(" Q:Can -> Mon (bar-inv)=")
show(stdout, "text/plain", Q_mat); print("\n")