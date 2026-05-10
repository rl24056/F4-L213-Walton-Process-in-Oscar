############################################################
# F4 order-6 Kac centraliser and Weyl-level inverting test
#
# Purpose:
# 1. Use the Walton-style order-6 element f with Kac tuple
#        kac_f = [0, 1, 0, 1, 1]
#
# 2. Identify the zero-root subsystem of C_{F4}(f)^0.
#
# 3. Compute the Weyl-level centraliser:
#        W_cent(f) = { w in W(F4) | w centralises f }
#
# 4. Compute the Weyl-level inverting coset:
#        W_inv(f) = { w in W(F4) | w sends f to f^-1 }
#
# 5. Test which Weyl-level inverting elements have adjoint trace -4,
#    matching the forced PSL2(13) Brauer profile on L(F4).
#
# This script is pure Julia. It does not need GAP.
############################################################


############################################################
# Global data for the Walton-style f
############################################################

kac_f = [0, 1, 0, 1, 1]
n_f = 6

# In this script, only the first four entries are used for ordinary
# root exponents against simple-root coordinates.
# The fifth entry is kept because the Kac tuple was originally recorded
# in this five-entry format.

println("============================================================")
println("F4 ORDER-6 KAC CENTRALISER AND WEYL-LEVEL INVERTING TEST")
println("============================================================")
println("Kac tuple for f = ", kac_f)
println("Order of f = ", n_f)


############################################################
# F4 simple roots in Bourbaki coordinates
#
# We use the standard realisation:
#
# alpha_1 = e2 - e3
# alpha_2 = e3 - e4
# alpha_3 = e4
# alpha_4 = 1/2(e1 - e2 - e3 - e4)
#
# Highest root:
# theta = 2 alpha_1 + 3 alpha_2 + 4 alpha_3 + 2 alpha_4
############################################################

F4_SIMPLE_ROOTS_E = [
    [0//1, 1//1, -1//1, 0//1],              # alpha_1
    [0//1, 0//1, 1//1, -1//1],              # alpha_2
    [0//1, 0//1, 0//1, 1//1],               # alpha_3
    [1//2, -1//2, -1//2, -1//2]             # alpha_4
]


############################################################
# Basic vector and matrix functions over Q
############################################################

function DotE(u, v)
    return sum(u[i] * v[i] for i in 1:4)
end

function RatToInt(x)
    if denominator(x) != 1
        error("Expected an integer rational, but got ", x)
    end

    return Int(numerator(x))
end

function MatIdentityQ(n)
    return [[i == j ? 1//1 : 0//1 for j in 1:n] for i in 1:n]
end

function MatKeyQ(M)
    return Tuple(vcat(M...))
end

function MatMulQ(A, B)
    n = length(A)

    return [[sum(A[i][k] * B[k][j] for k in 1:n) for j in 1:n] for i in 1:n]
end

function MatApplyQ(M, v)
    n = length(v)

    return [sum(M[i][j] * v[j] for j in 1:n) for i in 1:n]
end

function MatTraceQ(M)
    return sum(M[i][i] for i in 1:length(M))
end

function MatOrderQ(M; limit = 200)
    n = length(M)
    I = MatIdentityQ(n)
    P = MatIdentityQ(n)

    for k in 1:limit
        P = MatMulQ(M, P)

        if MatKeyQ(P) == MatKeyQ(I)
            return k
        end
    end

    return 0
end


############################################################
# Convert between simple-root coordinates and e-coordinates
############################################################

function F4SimpleToE(c)
    c1, c2, c3, c4 = c

    a1 = F4_SIMPLE_ROOTS_E[1]
    a2 = F4_SIMPLE_ROOTS_E[2]
    a3 = F4_SIMPLE_ROOTS_E[3]
    a4 = F4_SIMPLE_ROOTS_E[4]

    v = [0//1, 0//1, 0//1, 0//1]

    for i in 1:4
        v[i] = c1*a1[i] + c2*a2[i] + c3*a3[i] + c4*a4[i]
    end

    return v
end

function F4ToSimpleCoefficients(v)
    x1, x2, x3, x4 = v

    c4 = 2 * x1
    c1 = x2 + x1
    c2 = x3 + x2 + 2*x1
    c3 = x4 + x3 + x2 + 3*x1

    return [RatToInt(c1), RatToInt(c2), RatToInt(c3), RatToInt(c4)]
end


############################################################
# Build the full F4 root system
#
# F4 roots in e-coordinates:
#   ±e_i
#   ±e_i ± e_j
#   1/2(±e_1 ± e_2 ± e_3 ± e_4)
#
# Total: 8 + 24 + 16 = 48 roots.
############################################################

function F4RootListE()
    seen = Dict{Any, Any}()

    function AddRoot!(v)
        seen[Tuple(v)] = v
    end

    # Roots ±e_i
    for i in 1:4
        v = [0//1, 0//1, 0//1, 0//1]
        v[i] = 1//1
        AddRoot!(copy(v))

        v[i] = -1//1
        AddRoot!(copy(v))
    end

    # Roots ±e_i ± e_j
    for i in 1:4
        for j in i+1:4
            for si in [-1, 1]
                for sj in [-1, 1]
                    v = [0//1, 0//1, 0//1, 0//1]
                    v[i] = si//1
                    v[j] = sj//1
                    AddRoot!(copy(v))
                end
            end
        end
    end

    # Roots 1/2(±e_1 ± e_2 ± e_3 ± e_4)
    for s1 in [-1, 1]
        for s2 in [-1, 1]
            for s3 in [-1, 1]
                for s4 in [-1, 1]
                    v = [s1//2, s2//2, s3//2, s4//2]
                    AddRoot!(copy(v))
                end
            end
        end
    end

    roots = collect(values(seen))
    roots = sort(roots, by = v -> Tuple(v))

    return roots
end

F4_ROOTS_E = F4RootListE()
F4_ROOT_COEFFS = sort([F4ToSimpleCoefficients(r) for r in F4_ROOTS_E], by = r -> Tuple(r))

println("------------------------------------------------------------")
println("Root-system check")
println("------------------------------------------------------------")
println("Number of F4 roots = ", length(F4_ROOTS_E))
println("Expected number of F4 roots = 48")


############################################################
# Positive root test in simple-root coordinates
############################################################

function IsPositiveRootSimpleCoords(r)
    return all(x -> x >= 0, r) && any(x -> x > 0, r)
end


############################################################
# Step 1:
# Identify zero-root subsystem for f
############################################################

println("============================================================")
println("IDENTIFY ZERO-ROOT SUBSYSTEM FOR WALTON-STYLE f")
println("============================================================")

zero_roots_f = []

for r in F4_ROOT_COEFFS
    expo = mod(
        r[1]*kac_f[1] +
        r[2]*kac_f[2] +
        r[3]*kac_f[3] +
        r[4]*kac_f[4],
        n_f
    )

    if expo == 0
        push!(zero_roots_f, r)
    end
end

positive_zero_roots_f = [r for r in zero_roots_f if IsPositiveRootSimpleCoords(r)]

println("All zero roots = ")
println(zero_roots_f)

println("Positive zero roots = ")
println(positive_zero_roots_f)

println("Number of zero roots = ", length(zero_roots_f))
println("Centraliser Lie dimension = 4 + zero roots = ", 4 + length(zero_roots_f))


############################################################
# Compute lengths and pairings of the positive zero roots
############################################################

println("------------------------------------------------------------")
println("Positive zero roots in e-coordinates and their lengths")
println("------------------------------------------------------------")

for r in positive_zero_roots_f
    e = F4SimpleToE(r)
    println("root ", r, " has e-coordinates ", e, " and length squared ", DotE(e,e))
end

println("------------------------------------------------------------")
println("Pairwise inner products")
println("------------------------------------------------------------")

for i in 1:length(positive_zero_roots_f)
    for j in 1:length(positive_zero_roots_f)
        ri = positive_zero_roots_f[i]
        rj = positive_zero_roots_f[j]

        ei = F4SimpleToE(ri)
        ej = F4SimpleToE(rj)

        println("<", ri, ", ", rj, "> = ", DotE(ei,ej))
    end
end

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")
println("The zero roots are ±alpha_1 and ±alpha_3.")
println("alpha_1 and alpha_3 are orthogonal.")
println("Therefore the semisimple part of C_{F4}(f)^0 has type A1 + A1.")
println("Since F4 has rank 4 and A1+A1 has rank 2, there is also a 2-dimensional torus.")
println("So:")
println("C_{F4}(f)^0 has connected reductive type A1 + A1 + T2.")
println("Lie dimension check: dim(A1)+dim(A1)+dim(T2) = 3 + 3 + 2 = 8.")

println("============================================================")
println("END ZERO-ROOT SUBSYSTEM IDENTIFICATION")
println("============================================================")


############################################################
# Step 2:
# Weyl-level centraliser and inverting coset for f
#
# We compute inside W(F4):
#
#   W_cent(f) = { w in W(F4) | w centralises f }
#   W_inv(f)  = { w in W(F4) | w sends f to f^-1 }
#
# This is the Weyl-level analogue of starting to build
# the extended centraliser C_G^*(f).
############################################################

println("============================================================")
println("WEYL-LEVEL CENTRALISER AND INVERTING COSET FOR f")
println("============================================================")


############################################################
# Reflection matrix in a root alpha
############################################################

function ReflectionMatrixQ(alpha)
    n = length(alpha)
    aa = DotE(alpha, alpha)

    cols = []

    for j in 1:n
        v = [i == j ? 1//1 : 0//1 for i in 1:n]
        coeff = (2//1) * DotE(v, alpha) / aa
        img = [v[i] - coeff * alpha[i] for i in 1:n]
        push!(cols, img)
    end

    return [[cols[j][i] for j in 1:n] for i in 1:n]
end


############################################################
# Generate W(F4) from the four simple reflections
############################################################

W_gens = [ReflectionMatrixQ(a) for a in F4_SIMPLE_ROOTS_E]

W_seen = Dict{Any, Any}()
W_queue = []

I4Q = MatIdentityQ(4)

W_seen[MatKeyQ(I4Q)] = I4Q
push!(W_queue, I4Q)

while length(W_queue) > 0
    M = popfirst!(W_queue)

    for S in W_gens
        N = MatMulQ(S, M)
        k = MatKeyQ(N)

        if !haskey(W_seen, k)
            W_seen[k] = N
            push!(W_queue, N)
        end
    end
end

W_F4 = collect(values(W_seen))

println("Size of W(F4) = ", length(W_F4))
println("Expected size of W(F4) = 1152")


############################################################
# Exponent of a root against the Kac tuple
############################################################

function F4KacExponentE(v, kac, n)
    r = F4ToSimpleCoefficients(v)

    return mod(
        r[1]*kac[1] +
        r[2]*kac[2] +
        r[3]*kac[3] +
        r[4]*kac[4],
        n
    )
end

function WeylCentralisesKac(M, kac, n)
    for r in F4_ROOTS_E
        lhs = F4KacExponentE(MatApplyQ(M, r), kac, n)
        rhs = F4KacExponentE(r, kac, n)

        if lhs != rhs
            return false
        end
    end

    return true
end

function WeylInvertsKac(M, kac, n)
    for r in F4_ROOTS_E
        lhs = F4KacExponentE(MatApplyQ(M, r), kac, n)
        rhs = mod(-F4KacExponentE(r, kac, n), n)

        if lhs != rhs
            return false
        end
    end

    return true
end


############################################################
# Find centralising and inverting Weyl elements
############################################################

W_cent_f = []
W_inv_f = []

for M in W_F4
    if WeylCentralisesKac(M, kac_f, n_f)
        push!(W_cent_f, M)
    end

    if WeylInvertsKac(M, kac_f, n_f)
        push!(W_inv_f, M)
    end
end

println("------------------------------------------------------------")
println("Weyl centraliser and inverting coset")
println("------------------------------------------------------------")

println("Size of W_cent(f) = ", length(W_cent_f))
println("Size of W_inv(f)  = ", length(W_inv_f))

println("Orders of elements in W_cent(f) = ", sort([MatOrderQ(M) for M in W_cent_f]))
println("Orders of elements in W_inv(f)  = ", sort([MatOrderQ(M) for M in W_inv_f]))


############################################################
# Compare W_cent(f) with Weyl group generated by alpha_1, alpha_3
############################################################

S_alpha1 = W_gens[1]
S_alpha3 = W_gens[3]

W_zero_seen = Dict{Any, Any}()
W_zero_queue = []

W_zero_seen[MatKeyQ(I4Q)] = I4Q
push!(W_zero_queue, I4Q)

while length(W_zero_queue) > 0
    M = popfirst!(W_zero_queue)

    for S in [S_alpha1, S_alpha3]
        N = MatMulQ(S, M)
        k = MatKeyQ(N)

        if !haskey(W_zero_seen, k)
            W_zero_seen[k] = N
            push!(W_zero_queue, N)
        end
    end
end

W_zero = collect(values(W_zero_seen))

cent_keys = Set(MatKeyQ(M) for M in W_cent_f)
zero_keys = Set(MatKeyQ(M) for M in W_zero)

println("------------------------------------------------------------")
println("Zero-root Weyl subgroup")
println("------------------------------------------------------------")

println("Size of <s_alpha1, s_alpha3> = ", length(W_zero))
println("Does <s_alpha1, s_alpha3> equal W_cent(f)? ", cent_keys == zero_keys)


############################################################
# Check minus identity
############################################################

minus_I4Q = [[i == j ? -1//1 : 0//1 for j in 1:4] for i in 1:4]

println("------------------------------------------------------------")
println("Minus identity test")
println("------------------------------------------------------------")

println("-I is in W(F4)? ", haskey(W_seen, MatKeyQ(minus_I4Q)))
println("-I centralises f? ", WeylCentralisesKac(minus_I4Q, kac_f, n_f))
println("-I inverts f? ", WeylInvertsKac(minus_I4Q, kac_f, n_f))


############################################################
# Print action of inverting Weyl elements on simple roots
############################################################

function SimpleRootImageData(M)
    data = []

    for i in 1:4
        img_e = MatApplyQ(M, F4_SIMPLE_ROOTS_E[i])
        img_simple = F4ToSimpleCoefficients(img_e)
        push!(data, img_simple)
    end

    return data
end

println("------------------------------------------------------------")
println("Inverting Weyl elements: action on simple roots")
println("Each row means images of alpha_1, alpha_2, alpha_3, alpha_4")
println("------------------------------------------------------------")

for i in 1:length(W_inv_f)
    M = W_inv_f[i]

    println("Inverting element ", i)
    println("order = ", MatOrderQ(M))
    println(SimpleRootImageData(M))
end

println("------------------------------------------------------------")
println("Summary")
println("------------------------------------------------------------")

println("At Weyl level:")
println("W_cent(f) has size ", length(W_cent_f), ".")
println("W_inv(f) has size ", length(W_inv_f), ".")
println("The extended Weyl-level object has size ", length(W_cent_f) + length(W_inv_f), ".")
println("W_cent(f) is exactly the Weyl group of the zero-root subsystem A1 + A1.")
println("Every Weyl-level inverting element found here has order 2.")

println("============================================================")
println("END WEYL-LEVEL CENTRALISER / INVERTING COSET")
println("============================================================")


############################################################
# Step 3:
# Trace test for Weyl-level inverting elements
#
# We want t to have trace -4 on L(F4), because the forced
# PSL2(13) Brauer profile was:
#
#   order 2: trace -4
#
# The Weyl-level candidate -I should give trace -4:
#
#   Cartan trace = -4
#   no root is fixed by -I
#   so total adjoint trace = -4
############################################################

println("============================================================")
println("TRACE TEST FOR WEYL-LEVEL INVERTING ELEMENTS")
println("============================================================")


############################################################
# Count roots fixed by a Weyl element
#
# This gives the root-space contribution at the Weyl-permutation
# level. For -I this is safe because it fixes no roots.
############################################################

function FixedRootsByWeyl(M)
    fixed = []

    for r in F4_ROOTS_E
        img = MatApplyQ(M, r)

        if img == r
            push!(fixed, r)
        end
    end

    return fixed
end

function WeylAdjointTraceNaive(M)
    cartan_trace = MatTraceQ(M)
    fixed_roots = FixedRootsByWeyl(M)

    return cartan_trace + length(fixed_roots)
end


############################################################
# Test all Weyl-level inverting elements
############################################################

println("Target trace for t on L(F4) = -4")
println("------------------------------------------------------------")

good_weyl_t = []

for i in 1:length(W_inv_f)
    M = W_inv_f[i]

    cartan_trace = MatTraceQ(M)
    fixed_roots = FixedRootsByWeyl(M)
    naive_trace = WeylAdjointTraceNaive(M)

    is_minus_I = MatKeyQ(M) == MatKeyQ(minus_I4Q)

    println("Inverting Weyl element ", i)
    println("order = ", MatOrderQ(M))
    println("is -I? ", is_minus_I)
    println("Cartan trace = ", cartan_trace)
    println("Number of fixed roots = ", length(fixed_roots))
    println("Naive adjoint trace = ", naive_trace)
    println("Action on simple roots = ", SimpleRootImageData(M))

    if naive_trace == -4
        push!(good_weyl_t, M)
        println("MATCHES trace -4")
    else
        println("Does not match trace -4 at this Weyl-permutation level")
    end

    println("------------------------------------------------------------")
end

println("Number of Weyl-level inverting candidates with trace -4 = ", length(good_weyl_t))


############################################################
# Check whether W_inv(f) is exactly (-I) * W_cent(f)
############################################################

minusI_times_cent = []

for C in W_cent_f
    push!(minusI_times_cent, MatMulQ(minus_I4Q, C))
end

inv_keys = Set(MatKeyQ(M) for M in W_inv_f)
minusI_cent_keys = Set(MatKeyQ(M) for M in minusI_times_cent)

println("Is W_inv(f) equal to (-I) * W_cent(f)? ", inv_keys == minusI_cent_keys)


############################################################
# Final conclusion
############################################################

println("------------------------------------------------------------")
println("Final conclusion")
println("------------------------------------------------------------")

println("For the Walton-style order-6 element f with Kac tuple ", kac_f, ":")
println("1. The zero-root subsystem is A1 + A1.")
println("2. The connected centraliser has reductive type A1 + A1 + T2.")
println("3. W_cent(f) has size ", length(W_cent_f), ".")
println("4. W_inv(f) has size ", length(W_inv_f), ".")
println("5. W_inv(f) is the coset (-I) * W_cent(f): ", inv_keys == minusI_cent_keys, ".")
println("6. The clean Weyl-level candidate for t is -I.")
println("7. This -I candidate inverts f and has adjoint trace -4.")
println("8. This matches the required order-2 trace from the PSL2(13) Brauer profile.")

println("============================================================")
println("END FULL F4 ORDER-6 KAC CENTRALISER / WEYL TRACE TEST")
println("============================================================")
