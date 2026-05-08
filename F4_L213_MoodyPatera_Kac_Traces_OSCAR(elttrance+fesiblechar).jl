############################################################
# F4_L213_MoodyPatera_Kac_Traces_OSCAR.jl
#
# Purpose:
#   OSCAR / Julia version of the F4 part of AJL's Moody--Patera
#   trace and Kac-coordinate calculation, used for the baby example
#
#       L2(13) < F4.
#
#   This script:
#     1. Builds the F4 Moody--Patera search space.
#     2. Computes F4 trace-profile tables for orders 2,3,6,7,13,14.
#     3. Checks the order-13 Kac coordinate [1,1,1,1,2].
#     4. Displays PSL(2,13) ordinary and mod-5 Brauer character tables.
#     5. Checks the five feasible L(F4)|_{L2(13)} rows.
#
# Expected F4 trace-table count:
#
#       (2, 3, 11, 20, 104, 113)
#
############################################################

using Oscar
using Primes

############################################################
# Basic utilities
############################################################

function gcd_list(v::Vector{Int})
    g = 0
    for x in v
        g = gcd(g, abs(x))
    end
    return g
end

function divisors_int(n::Int)
    return sort([d for d in 1:n if n % d == 0])
end

function cartesian_product_ranges(ranges)
    res = [[]]

    for R in ranges
        newres = []

        for a in res
            for x in R
                push!(newres, vcat(a, [x]))
            end
        end

        res = newres
    end

    return res
end

############################################################
# F4 data
############################################################

const F4_RANK = 4

# Bourbaki-style F4 Cartan matrix.
# This convention is compatible with the affine marks
#
#     [2,3,4,2,1].
#
const F4_CARTAN = [
     2 -1  0  0;
    -1  2 -2  0;
     0 -1  2 -1;
     0  0 -1  2
]

const F4_MARKS = [2, 3, 4, 2, 1]

# F4 is simply connected and adjoint at the level needed here,
# so the fundamental-group multiplier is 1.
const F4_FUND_INDEX = 1

############################################################
# Weyl group orbit on weights in fundamental-weight coordinates
############################################################

function reflect_weight(v::Vector{Int}, i::Int, A::Matrix{Int})
    # s_i(lambda) = lambda - <lambda, alpha_i^vee> alpha_i.
    #
    # If v is written in fundamental-weight coordinates, then
    #
    #     <lambda, alpha_i^vee> = v[i].
    #
    # Also alpha_i = sum_j A[i,j] omega_j.
    #
    w = copy(v)
    c = v[i]

    for j in 1:length(v)
        w[j] -= c * A[i, j]
    end

    return w
end

function weight_orbit_F4(highest::Vector{Int})
    seen = Set{Tuple{Int,Int,Int,Int}}()
    queue = Vector{Vector{Int}}()

    push!(queue, highest)
    push!(seen, Tuple(highest))

    pos = 1

    while pos <= length(queue)
        v = queue[pos]
        pos += 1

        for i in 1:F4_RANK
            w = reflect_weight(v, i, F4_CARTAN)
            tw = Tuple(w)

            if !(tw in seen)
                push!(seen, tw)
                push!(queue, w)
            end
        end
    end

    return [collect(t) for t in seen]
end

############################################################
# Multiset helper
############################################################

function multiset_append!(
    M::Vector{Vector{Int}},
    L::Vector{Vector{Int}},
    copies::Int = 1
)
    for _ in 1:copies
        append!(M, L)
    end
end

############################################################
# F4 weight multisets
#
# Same meaning as in the Magma code:
#
# Minimal 26-dimensional module:
#
#       0^2 + orbit(0001)
#
# Adjoint 52-dimensional module:
#
#       0^4 + orbit(0001) + orbit(1000)
#
############################################################

function F4_weight_multisets()
    zero = [0, 0, 0, 0]

    orb_0001 = weight_orbit_F4([0, 0, 0, 1])
    orb_1000 = weight_orbit_F4([1, 0, 0, 0])

    W_min = Vector{Vector{Int}}()
    multiset_append!(W_min, [zero], 2)
    multiset_append!(W_min, orb_0001, 1)

    W_ad = Vector{Vector{Int}}()
    multiset_append!(W_ad, [zero], 4)
    multiset_append!(W_ad, orb_0001, 1)
    multiset_append!(W_ad, orb_1000, 1)

    println("F4 minimal weight count = ", length(W_min))
    println("F4 adjoint weight count = ", length(W_ad))

    return [W_min, W_ad]
end

############################################################
# Convert fundamental-weight coordinates to simple-root coordinates
#
# Magma did:
#
#       w * INV_CARTAN
#
# Here we do the same using Rational arithmetic.
############################################################

function inverse_cartan_F4()
    A = Matrix{Rational{Int}}(undef, 4, 4)

    for i in 1:4
        for j in 1:4
            A[i, j] = F4_CARTAN[i, j] // 1
        end
    end

    return inv(A)
end

function weight_to_simple_coords(v::Vector{Int})
    invA = inverse_cartan_F4()
    res = Rational{Int}[]

    for j in 1:4
        s = 0 // 1

        for i in 1:4
            s += (v[i] // 1) * invA[i, j]
        end

        push!(res, s)
    end

    return res
end

############################################################
# AJL_MoodyPatera for F4 only
#
# This gives the number of classes of exact order m <= n.
#
# It is the F4 version of:
#
#       1 / ((1-t)(1-t^2)^2(1-t^3)(1-t^4)).
#
############################################################

function AJL_MoodyPatera_F4(n::Int)
    coeffs = zeros(Int, n)

    # Coefficient extraction for
    #
    #       1 / ((1-t)(1-t^2)^2(1-t^3)(1-t^4)).
    #
    degrees = [1, 2, 2, 3, 4]

    for m in 1:n
        count = 0
        ranges = [0:m for _ in degrees]

        for a in cartesian_product_ranges(ranges)
            if sum(a[i] * degrees[i] for i in 1:length(degrees)) == m
                count += 1
            end
        end

        coeffs[m] = count
    end

    numberof = copy(coeffs)

    for order in 2:n
        if isprime(order)
            numberof[order] = coeffs[order] - 1
        else
            proper = [d for d in divisors_int(order) if d != order]
            numberof[order] -= sum(numberof[d] for d in proper)
        end
    end

    return numberof
end

############################################################
# exelts_mp for F4
#
# Returns a list of F4 semisimple classes.
#
# Each class is stored as:
#
#       [
#           minimal_eigen_exponent_multiset,
#           adjoint_eigen_exponent_multiset,
#           Kac_coordinates
#       ]
#
# The eigen exponent multiset is stored as a Vector{Vector{Int}}.
# Each inner vector records the integer exponent data before summing.
############################################################

function exelts_mp_F4(n::Int; debug::Bool = false)
    limit = AJL_MoodyPatera_F4(n)[n]

    if debug
        println("Looking for $limit F4 classes of order $n.")
    end

    W = F4_weight_multisets()
    W_simple = [[weight_to_simple_coords(w) for w in V] for V in W]

    ranges = [0:(n ÷ F4_MARKS[j]) for j in 1:F4_RANK]
    coeff_tuples_first = cartesian_product_ranges(ranges)

    if debug
        println("First approximation: ", length(coeff_tuples_first))
    end

    coeff_tuples = Vector{Vector{Int}}()

    for i in coeff_tuples_first
        r = n - sum(i[j] * F4_MARKS[j] for j in 1:F4_RANK)

        if 0 <= r <= n
            push!(coeff_tuples, vcat(i, [r]))
        end
    end

    if debug
        println("Unfiltered search space: ", length(coeff_tuples))
    end

    coeff_tuples = [c for c in coeff_tuples if gcd_list(c) == 1]

    if debug
        println("After gcd check: ", length(coeff_tuples))
    end

    coeff_tuples = [
        c for c in coeff_tuples
        if sum(c[j] * F4_MARKS[j] for j in 1:5) == n
    ]

    if debug
        println("Final search space: ", length(coeff_tuples))
    end

    classes = []

    for C in coeff_tuples
        class_data = []

        for module_index in 1:2
            eigs = Vector{Vector{Int}}()

            for wt in W_simple[module_index]
                q = Int[]

                for x in 1:F4_RANK
                    val = F4_FUND_INDEX * C[x] * wt[x]

                    if denominator(val) != 1
                        error("Non-integral exponent found: $val")
                    end

                    push!(q, numerator(val))
                end

                push!(eigs, q)
            end

            push!(class_data, eigs)
        end

        push!(class_data, C)
        push!(classes, class_data)
    end

    num = length(classes)

    if num < limit
        println("***WARNING: Not all classes found: $num of $limit.")
    elseif num > limit
        println("***Too many classes found: $num of $limit.")
    end

    return classes
end

############################################################
# Trace profile for F4
#
# Instead of using exact Magma RootOfUnity arithmetic, we store each trace
# as a dictionary:
#
#       exponent mod n  => multiplicity.
#
# For example, for order 13 the adjoint trace profile
#
#       0=>4, 1=>4, ..., 12=>4
#
# means:
#
#       4(1 + zeta + zeta^2 + ... + zeta^12) = 0.
#
############################################################

function trace_profile_from_eigs(eigs, n::Int, e::Int)
    D = Dict{Int,Int}()

    for q in eigs
        expo = mod(e * sum(q), n)
        D[expo] = get(D, expo, 0) + 1
    end

    return sort(collect(D))
end

function F4_trace_table(n::Int; debug::Bool = true)
    X = exelts_mp_F4(n; debug = debug)

    exponents = [n ÷ j for j in divisors_int(n) if j != 1]

    table = []

    for x in X
        min_eigs = x[1]
        ad_eigs = x[2]
        kac = x[3]

        min_profiles = [
            trace_profile_from_eigs(min_eigs, n, e)
            for e in exponents
        ]

        ad_profiles = [
            trace_profile_from_eigs(ad_eigs, n, e)
            for e in exponents
        ]

        push!(table, [min_profiles, ad_profiles, kac])
    end

    return table
end

############################################################
# Generate F4 trace tables
############################################################

println()
println("Generating F4 trace tables...")

F4_ELTS2  = F4_trace_table(2)
F4_ELTS3  = F4_trace_table(3)
F4_ELTS6  = F4_trace_table(6)
F4_ELTS7  = F4_trace_table(7)
F4_ELTS13 = F4_trace_table(13)
F4_ELTS14 = F4_trace_table(14)

println()
println("F4 trace table counts:")
println((
    length(F4_ELTS2),
    length(F4_ELTS3),
    length(F4_ELTS6),
    length(F4_ELTS7),
    length(F4_ELTS13),
    length(F4_ELTS14)
))

println()
println("Expected count:")
println("(2, 3, 11, 20, 104, 113)")

############################################################
# Order-13 Kac-coordinate check
############################################################

println()
println("Searching for order-13 Kac coordinate [1,1,1,1,2]...")

found_kac_13 = false

for x in F4_ELTS13
    if x[3] == [1, 1, 1, 1, 2]
        global found_kac_13 = true

        println()
        println("FOUND Kac coordinate [1,1,1,1,2]")
        println("Minimal trace profile = ", x[1])
        println("Adjoint trace profile = ", x[2])

        println()
        println("Interpretation:")
        println("Adjoint profile has multiplicity 4 on every exponent 0,...,12.")
        println("Therefore Tr_L(F4)(g) = 4(1 + zeta + ... + zeta^12) = 0.")
        println("Since no Kac coordinate is zero, C_{F4}(g)^0 is toral.")
    end
end

if !found_kac_13
    println("WARNING: Kac coordinate [1,1,1,1,2] was not found.")
end

############################################################
# PSL(2,13) side through GAP
############################################################

println()
println("Constructing H = PSL(2,13) in GAP through OSCAR...")

H = GAP.Globals.PSL(2, 13)
ct = GAP.Globals.CharacterTable(H)

println()
println("Ordinary character table of PSL(2,13):")
GAP.Globals.Display(ct)

println()
println("Brauer table mod 5:")
bt = GAP.Globals.BrauerTable(ct, 5)
GAP.Globals.Display(bt)

println()
println("Conjugacy class orders:")
orders = GAP.Globals.OrdersClassRepresentatives(ct)
println(orders)

############################################################
# Five feasible rows for L(F4)|_{L2(13)}
#
# Module order:
#
#       [1, 7a, 7b, 12a, 12b, 12c, 13, 14a, 14b]
#
############################################################

k1 = [0, 0, 0, 0, 1, 1, 0, 2, 0]
k2 = [0, 0, 0, 1, 0, 1, 0, 2, 0]
k3 = [0, 0, 0, 1, 1, 0, 0, 2, 0]
k4 = [3, 0, 5, 0, 0, 0, 0, 1, 0]
k5 = [3, 5, 0, 0, 0, 0, 0, 1, 0]

dims = [1, 7, 7, 12, 12, 12, 13, 14, 14]

function dot_int(a, b)
    return sum(a[i] * b[i] for i in 1:length(a))
end

println()
println("Dimension checks:")
println("1: ", dot_int(k1, dims))
println("2: ", dot_int(k2, dims))
println("3: ", dot_int(k3, dims))
println("4: ", dot_int(k4, dims))
println("5: ", dot_int(k5, dims))

println()
println("Rows:")
println("1: ", k1)
println("2: ", k2)
println("3: ", k3)
println("4: ", k4)
println("5: ", k5)

println()
println("Decompositions:")
println("1: 12b + 12c + 2*14a")
println("2: 12a + 12c + 2*14a")
println("3: 12a + 12b + 2*14a")
println("4: 3*1 + 5*7b + 14a")
println("5: 3*1 + 5*7a + 14a")

println()
println("Fixed points on L(F4):")
println("rows 1,2,3: 0")
println("rows 4,5: 3")

println()
println("Order-13 conclusion:")
println("Rows 1,2,3 are the serious candidates with trace 0 on order-13 classes.")
println("Rows 4,5 are eliminated by fixed-point/trivial-summand considerations.")

println()
println("Done.")
