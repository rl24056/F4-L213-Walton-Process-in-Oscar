############################################################
# F4_L2_13_char7_hybrid_torus_normaliser_all_f_Bruhat_t_search.jl
#
# Purpose:
#   One-piece OSCAR/Julia script for the F4 characteristic-7
#   Walton-style hybrid torus-normaliser search.
#
# This script combines the blocks for:
#   1. Building F4 roots in e-coordinates.
#   2. Building the Weyl group W(F4).
#   3. Defining the split torus-normaliser model T_6 . W(F4).
#   4. Defining adjoint trace functions on L(F4).
#   5. Searching for corrected order-6 f-candidates normalising
#      the order-13 torus element g by exponent 10.
#   6. Building B = <g,f> in the hybrid model and checking |B| = 78.
#   7. Searching first for pure Weyl Bruhat-type involutions t.
#   8. Searching for torus-part Bruhat-type involutions t.
#   9. Searching all corrected f-candidates for possible Bruhat t.
#  10. Re-running the corrected all-f search without imposing the
#      wrong fixed-vector condition on the mod-6 torus part of t.
#
# Run in a fresh Julia session with OSCAR installed:
#
#   julia
#   include("F4_L2_13_char7_hybrid_torus_normaliser_all_f_Bruhat_t_search.jl")
#
# Or paste the whole file after:
#
#   using Oscar
############################################################

using Oscar

############################################################
# SETUP BLOCK FOR NEW OSCAR/JULIA SESSION
#
# This defines:
#   F4 roots
#   Weyl group W(F4)
#   torus-normaliser model T_6 . W(F4)
#   trace functions on L(F4)
#   torus vectors in (Z/6Z)^4
############################################################

println("============================================================")
println("F4 TORUS-NORMALISER SETUP FOR NEW OSCAR SESSION")
println("============================================================")

############################################################
# PART 1.
# F4 roots in e-coordinates
############################################################

function F4RootListE()
    roots = Vector{Vector{Rational{Int}}}()

    # short roots: +/- e_i
    for i in 1:4
        for s in [-1, 1]
            v = [0//1, 0//1, 0//1, 0//1]
            v[i] = s//1
            push!(roots, v)
        end
    end

    # long roots: +/- e_i +/- e_j
    for i in 1:4
        for j in i+1:4
            for si in [-1, 1]
                for sj in [-1, 1]
                    v = [0//1, 0//1, 0//1, 0//1]
                    v[i] = si//1
                    v[j] = sj//1
                    push!(roots, v)
                end
            end
        end
    end

    # half roots: 1/2(+-e1 +-e2 +-e3 +-e4)
    for s1 in [-1, 1]
        for s2 in [-1, 1]
            for s3 in [-1, 1]
                for s4 in [-1, 1]
                    push!(roots, [s1//2, s2//2, s3//2, s4//2])
                end
            end
        end
    end

    return roots
end

function DotE(u, v)
    return sum(u[i]*v[i] for i in 1:4)
end

############################################################
# Bourbaki F4 simple roots:
#
# alpha_1 = e2 - e3
# alpha_2 = e3 - e4
# alpha_3 = e4
# alpha_4 = 1/2(e1 - e2 - e3 - e4)
#
# Convert e-coordinates to simple-root coordinates.
############################################################

function F4ToSimpleCoefficients(v)
    x1, x2, x3, x4 = v

    c1 = x1 + x2
    c2 = 2*x1 + x2 + x3
    c3 = 3*x1 + x2 + x3 + x4
    c4 = 2*x1

    cs = [c1, c2, c3, c4]

    for c in cs
        if denominator(c) != 1
            error("Non-integral simple-root coefficient found.")
        end
    end

    return [Int(c) for c in cs]
end

F4_ROOTS_E_FOR_W = F4RootListE()
F4_ROOT_COEFFS = [F4ToSimpleCoefficients(v) for v in F4_ROOTS_E_FOR_W]

println("Number of F4 roots = ", length(F4_ROOTS_E_FOR_W))
println("Expected number of F4 roots = 48")

############################################################
# PART 2.
# Matrix functions over Q
############################################################

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

function MatTransposeQ(M)
    n = length(M)

    return [[M[j][i] for j in 1:n] for i in 1:n]
end

function IntFromQ(x)
    if denominator(x) != 1
        error("Expected an integer rational.")
    end

    return Int(numerator(x))
end

function ReflectionMatrixQ(alpha)
    n = length(alpha)
    aa = DotE(alpha, alpha)

    cols = []

    for j in 1:n
        v = [i == j ? 1//1 : 0//1 for i in 1:n]
        coeff = 2 * DotE(v, alpha) // aa
        img = [v[i] - coeff * alpha[i] for i in 1:n]
        push!(cols, img)
    end

    return [[cols[j][i] for j in 1:n] for i in 1:n]
end

function MatOrderQ(M; limit = 500)
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
# PART 3.
# Build W(F4)
############################################################

F4_SIMPLE_ROOTS_E = [
    [0//1, 1//1, -1//1, 0//1],              # alpha_1
    [0//1, 0//1, 1//1, -1//1],              # alpha_2
    [0//1, 0//1, 0//1, 1//1],               # alpha_3
    [1//2, -1//2, -1//2, -1//2]             # alpha_4
]

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

function SimpleRootImageData(M)
    data = []

    for i in 1:4
        img_e = MatApplyQ(M, F4_SIMPLE_ROOTS_E[i])
        img_simple = F4ToSimpleCoefficients(img_e)
        push!(data, img_simple)
    end

    return data
end

############################################################
# PART 4.
# Split torus-normaliser model over F7
#
# Since q = 7, F7^* has order 6.
# Torus elements are exponent vectors in (Z/6Z)^4.
############################################################

n_torus = 6

function WeylActionOnTorusVector(M, a, n)
    Minv = MatTransposeQ(M)
    out = []

    for i in 1:4
        beta_e = MatApplyQ(Minv, F4_SIMPLE_ROOTS_E[i])
        beta_simple = F4ToSimpleCoefficients(beta_e)

        expo = 0

        for j in 1:4
            expo += beta_simple[j] * a[j]
        end

        push!(out, mod(expo, n))
    end

    return out
end

function TorusVectorAdd(a, b, n)
    return [mod(a[i] + b[i], n) for i in 1:length(a)]
end

function TorusVectorNeg(a, n)
    return [mod(-a[i], n) for i in 1:length(a)]
end

function TW_Mul(x, y, n)
    a, w = x
    b, v = y

    wb = WeylActionOnTorusVector(w, b, n)
    new_a = TorusVectorAdd(a, wb, n)
    new_w = MatMulQ(w, v)

    return (new_a, new_w)
end

function TW_IsIdentity(x, n)
    a, w = x

    return all(ai -> mod(ai,n) == 0, a) && MatKeyQ(w) == MatKeyQ(I4Q)
end

function TW_Order(a, w, n; limit = 500)
    x = (a, w)
    p = ([0,0,0,0], I4Q)

    for k in 1:limit
        p = TW_Mul(p, x, n)

        if TW_IsIdentity(p, n)
            return k
        end
    end

    return 0
end

function TW_Inverse(x, n)
    a, w = x

    winv = MatTransposeQ(w)
    minus_a = TorusVectorNeg(a, n)

    inv_a = WeylActionOnTorusVector(winv, minus_a, n)

    return (inv_a, winv)
end

function TW_Key(x, n)
    a, w = x

    return (Tuple([mod(ai, n) for ai in a]), MatKeyQ(w))
end

function TW_Equal(x, y, n)
    return TW_Key(x, n) == TW_Key(y, n)
end

function TW_Pow(x, k, n)
    out = ([0,0,0,0], I4Q)

    if k == 0
        return out
    end

    for i in 1:k
        out = TW_Mul(out, x, n)
    end

    return out
end

############################################################
# PART 5.
# Trace functions on L(F4)
############################################################

function RootExponentOnTorusVector(r_e, a, n)
    r_simple = F4ToSimpleCoefficients(r_e)

    expo = 0

    for j in 1:4
        expo += r_simple[j] * a[j]
    end

    return mod(expo, n)
end

function TW_AdjointTrace(a, w, n)
    cartan_trace = IntFromQ(MatTraceQ(w))
    zsum = complex(float(cartan_trace), 0.0)

    for r in F4_ROOTS_E_FOR_W
        img = MatApplyQ(w, r)

        if img == r
            expo = RootExponentOnTorusVector(r, a, n)
            zsum += cis(2*pi*expo/n)
        end
    end

    return round(Int, real(zsum))
end

function TW_PowerTraceProfileOrder6(a, w)
    x = (a, w)

    x1 = x
    x2 = TW_Mul(x1, x1, n_torus)
    x3 = TW_Mul(x2, x1, n_torus)

    tr1 = TW_AdjointTrace(x1[1], x1[2], n_torus)
    tr2 = TW_AdjointTrace(x2[1], x2[2], n_torus)
    tr3 = TW_AdjointTrace(x3[1], x3[2], n_torus)

    return [tr1, tr2, tr3]
end

############################################################
# PART 6.
# Torus vectors in (Z/6Z)^4
############################################################

torus_vectors_6 = []

for a1 in 0:5
    for a2 in 0:5
        for a3 in 0:5
            for a4 in 0:5
                push!(torus_vectors_6, [a1,a2,a3,a4])
            end
        end
    end
end

println("Number of torus vectors in (Z/6Z)^4 = ", length(torus_vectors_6))
println("Expected = 1296")

############################################################
# PART 7.
# Helpers for action on order-13 Kac vector
############################################################

function WeylActionOnVectorModN(w, u, n)
    return WeylActionOnTorusVector(w, u, n)
end

function ScalarVectorModN(c, u, n)
    return [mod(c*u[i], n) for i in 1:length(u)]
end

function WeylActionExponentOnG13(w, gvec)
    image = WeylActionOnVectorModN(w, gvec, 13)

    for k in 1:12
        if image == ScalarVectorModN(k, gvec, 13)
            return k
        end
    end

    return 0
end

############################################################
# Quick sanity check
############################################################

println("------------------------------------------------------------")
println("SETUP SANITY CHECK")
println("------------------------------------------------------------")

g13_vec_test = [1,1,1,1]

action_exponents = Dict{Int, Int}()

for w in W_F4
    e = WeylActionExponentOnG13(w, g13_vec_test)
    action_exponents[e] = get(action_exponents, e, 0) + 1
end

println("Action exponent distribution on g13_vec = [1,1,1,1]:")
for k in sort(collect(keys(action_exponents)))
    println("  exponent ", k, ": ", action_exponents[k])
end

println("============================================================")
println("END SETUP BLOCK")
println("============================================================")

############################################################
# NEXT STEP:
# Search for a genuine normalising f for the order-13 g
#
# The previous same-torus test failed because pure-torus f
# centralised g. In PSL2(13), f must act on <g> by exponent 10.
#
# So now search elements:
#
#   f = (a,w) in T_6 . W(F4)
#
# such that:
#
#   w(g13_vec) = 10*g13_vec mod 13
#   order(f) = 6
#   trace(f)   =  2
#   trace(f^2) = -2
#   trace(f^3) = -4
#
# This is the corrected torus-normaliser search for the 13:6 part.
############################################################

println("============================================================")
println("SEARCH FOR NORMALISING f WITH ACTION EXPONENT 10 ON g")
println("============================================================")

g13_vec = [1, 1, 1, 1]
target_action_exponent = 10
target_f_profile = [2, -2, -4]    # [trace(f), trace(f^2), trace(f^3)]

############################################################
# First find Weyl elements acting on g by exponent 10
############################################################

W_action10 = []

for w in W_F4
    expn = WeylActionExponentOnG13(w, g13_vec)

    if expn == target_action_exponent
        push!(W_action10, w)
    end
end

println("Number of Weyl elements sending g to g^10 = ", length(W_action10))

println("Orders of these Weyl elements:")
println(sort([MatOrderQ(w) for w in W_action10]))

println("------------------------------------------------------------")
println("Weyl elements acting by exponent 10")
println("------------------------------------------------------------")

for i in 1:length(W_action10)
    w = W_action10[i]
    println("W_action10 element ", i)
    println("  Weyl order = ", MatOrderQ(w))
    println("  action exponent on g = ", WeylActionExponentOnG13(w, g13_vec))
    println("  simple-root action = ", SimpleRootImageData(w))
    println("------------------------------------------------------------")
end

############################################################
# Search all torus parts a for f = (a,w)
############################################################

normalising_f_candidates = []

for wi in 1:length(W_action10)
    w = W_action10[wi]

    local_count = 0

    for a in torus_vectors_6
        ord = TW_Order(a, w, n_torus)

        if ord != 6
            continue
        end

        prof = TW_PowerTraceProfileOrder6(a, w)

        if prof == target_f_profile
            push!(normalising_f_candidates, (a, wi, w, prof))
            local_count += 1
        end
    end

    if local_count > 0
        println("W_action10 element ", wi, " produced ", local_count, " candidates.")
        println("  Weyl order = ", MatOrderQ(w))
        println("  action on simple roots = ", SimpleRootImageData(w))
    end
end

println("------------------------------------------------------------")
println("Normalising f candidates")
println("------------------------------------------------------------")

println("Total number of f candidates = ", length(normalising_f_candidates))

for i in 1:min(30, length(normalising_f_candidates))
    a, wi, w, prof = normalising_f_candidates[i]

    println("Candidate ", i)
    println("  torus vector a = ", a)
    println("  W_action10 index = ", wi)
    println("  Weyl order = ", MatOrderQ(w))
    println("  order(f) = ", TW_Order(a, w, n_torus))
    println("  trace profile [f,f^2,f^3] = ", prof)
    println("  action exponent on g = ", WeylActionExponentOnG13(w, g13_vec))
    println("  simple-root action = ", SimpleRootImageData(w))
    println("------------------------------------------------------------")
end

############################################################
# Store first candidate for the next step if it exists
############################################################

if length(normalising_f_candidates) > 0
    f_candidate_1 = normalising_f_candidates[1]
    f_a_1, f_wi_1, f_w_1, f_prof_1 = f_candidate_1

    f_TW_corrected = (f_a_1, f_w_1)

    println("Stored first corrected f candidate as f_TW_corrected.")
    println("f_TW_corrected torus vector = ", f_a_1)
    println("f_TW_corrected Weyl action = ", SimpleRootImageData(f_w_1))
else
    println("No corrected f candidate found with this exact trace profile.")
end

############################################################
# Summary
############################################################

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")
println("This is the corrected 13:6 search.")
println("If candidates appear, these are better f-candidates than the pure torus f.")
println("The next step is to build B = <g,f> in the hybrid model and check that")
println("f acts on g by exponent 10, so <g,f> has the expected 13:6 structure.")

println("============================================================")
println("END NORMALISING f SEARCH")
println("============================================================")

############################################################
# NEXT STEP:
# Build B = <g,f> in the hybrid torus-normaliser model
#
# We now use:
#
#   g = order-13 torus element with vector [1,1,1,1] mod 13
#   f = corrected normalising element found above
#
# The goal is to check:
#
#   order(g) = 13
#   order(f) = 6
#   f*g*f^{-1} = g^10
#   |<g,f>| = 78
#
# This is the required 13:6 local subgroup.
############################################################

println("============================================================")
println("BUILD B = <g,f> IN THE HYBRID MODEL")
println("============================================================")

############################################################
# Hybrid element:
#
#   (u, a, w)
#
# where:
#   u is the order-13 torus vector mod 13
#   a is the order-6 torus vector mod 6
#   w is a Weyl group element
############################################################

function HybridVectorAdd(x, y, n)
    return [mod(x[i] + y[i], n) for i in 1:length(x)]
end

function Hybrid_Mul(x, y)
    u1, a1, w1 = x
    u2, a2, w2 = y

    wu2 = WeylActionOnTorusVector(w1, u2, 13)
    wa2 = WeylActionOnTorusVector(w1, a2, 6)

    new_u = HybridVectorAdd(u1, wu2, 13)
    new_a = HybridVectorAdd(a1, wa2, 6)
    new_w = MatMulQ(w1, w2)

    return (new_u, new_a, new_w)
end

function Hybrid_Identity()
    return ([0,0,0,0], [0,0,0,0], I4Q)
end

function Hybrid_Key(x)
    u, a, w = x

    return (
        Tuple([mod(ui,13) for ui in u]),
        Tuple([mod(ai,6) for ai in a]),
        MatKeyQ(w)
    )
end

function Hybrid_IsIdentity(x)
    return Hybrid_Key(x) == Hybrid_Key(Hybrid_Identity())
end

function Hybrid_Pow(x, k)
    out = Hybrid_Identity()

    if k == 0
        return out
    end

    for i in 1:k
        out = Hybrid_Mul(out, x)
    end

    return out
end

function Hybrid_Order(x; limit = 1000)
    out = Hybrid_Identity()

    for k in 1:limit
        out = Hybrid_Mul(out, x)

        if Hybrid_IsIdentity(out)
            return k
        end
    end

    return 0
end

function Hybrid_Inverse(x)
    u, a, w = x

    winv = MatTransposeQ(w)

    minus_u = [mod(-ui,13) for ui in u]
    minus_a = [mod(-ai,6) for ai in a]

    inv_u = WeylActionOnTorusVector(winv, minus_u, 13)
    inv_a = WeylActionOnTorusVector(winv, minus_a, 6)

    return (inv_u, inv_a, winv)
end

function Hybrid_Conjugate(x, y)
    return Hybrid_Mul(Hybrid_Mul(x, y), Hybrid_Inverse(x))
end

function Hybrid_GroupGeneratedBy(gens)
    seen = Dict{Any, Any}()
    queue = []

    id = Hybrid_Identity()

    seen[Hybrid_Key(id)] = id
    push!(queue, id)

    full_gens = copy(gens)

    for g in gens
        push!(full_gens, Hybrid_Inverse(g))
    end

    while !isempty(queue)
        x = popfirst!(queue)

        for s in full_gens
            y = Hybrid_Mul(x, s)
            ky = Hybrid_Key(y)

            if !haskey(seen, ky)
                seen[ky] = y
                push!(queue, y)
            end
        end
    end

    return collect(values(seen))
end

############################################################
# Define g and corrected f
############################################################

zero13 = [0,0,0,0]
zero6 = [0,0,0,0]

g13_vec = [1,1,1,1]

g_hybrid = (g13_vec, zero6, I4Q)

# f_TW_corrected was stored by the previous block:
#   f_TW_corrected = (f_a_1, f_w_1)

f_a_corrected, f_w_corrected = f_TW_corrected
f_hybrid = (zero13, f_a_corrected, f_w_corrected)

println("g vector mod 13 = ", g13_vec)
println("f torus vector mod 6 = ", f_a_corrected)
println("f Weyl action = ", SimpleRootImageData(f_w_corrected))

println("------------------------------------------------------------")
println("Orders")
println("------------------------------------------------------------")

println("order(g) = ", Hybrid_Order(g_hybrid))
println("order(f) = ", Hybrid_Order(f_hybrid))

############################################################
# Check f*g*f^{-1} = g^10
############################################################

conj_g_by_f = Hybrid_Conjugate(f_hybrid, g_hybrid)
g_power_10 = Hybrid_Pow(g_hybrid, 10)

println("------------------------------------------------------------")
println("Action of f on <g>")
println("------------------------------------------------------------")

println("Does f*g*f^{-1} = g^10? ", Hybrid_Key(conj_g_by_f) == Hybrid_Key(g_power_10))

println("f*g*f^{-1} key = ", Hybrid_Key(conj_g_by_f))
println("g^10 key       = ", Hybrid_Key(g_power_10))

############################################################
# Build B = <g,f>
############################################################

B_hybrid = Hybrid_GroupGeneratedBy([g_hybrid, f_hybrid])

println("------------------------------------------------------------")
println("Group B = <g,f>")
println("------------------------------------------------------------")

println("|<g,f>| = ", length(B_hybrid))
println("Expected = 78")

############################################################
# Element order distribution in B
############################################################

order_distribution_B = Dict{Int, Int}()

for x in B_hybrid
    ord = Hybrid_Order(x)
    order_distribution_B[ord] = get(order_distribution_B, ord, 0) + 1
end

println("Element order distribution in B:")
for k in sort(collect(keys(order_distribution_B)))
    println("  order ", k, ": ", order_distribution_B[k])
end

############################################################
# Check powers of f acting on g
############################################################

println("------------------------------------------------------------")
println("Action exponents of powers of f on g")
println("------------------------------------------------------------")

for j in 0:5
    fj = Hybrid_Pow(f_hybrid, j)
    conj = Hybrid_Conjugate(fj, g_hybrid)

    found_exp = -1

    for k in 0:12
        if Hybrid_Key(conj) == Hybrid_Key(Hybrid_Pow(g_hybrid, k))
            found_exp = k
            break
        end
    end

    println("f^", j, " sends g to g^", found_exp)
end

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")

println("This confirms that the corrected f gives the required 13:6 local subgroup.")
println("So the local Borel-type subgroup B = <g,f> is now present in the hybrid model.")
println("The next step is to search for a Bruhat-type involution t with order 2, trace -4,")
println("and some b in B such that b*t has order 3.")

println("============================================================")
println("END BUILD B = <g,f>")
println("============================================================")

############################################################
# NEXT STEP:
# Search for pure Weyl Bruhat-type involutions t
#
# We already have:
#
#   g_hybrid
#   f_hybrid
#   B_hybrid = <g,f>, size 78
#
# Now we first test t of the simple form:
#
#   t = (0,0,w)
#
# where w is a Weyl element.
#
# Conditions:
#
#   order(t) = 2
#   trace(t on L(F4)) = -4
#   t*f*t^{-1} = f^{-1}
#   t does not normalise <g>
#   there exists b in B = <g,f> such that order(b*t) = 3
#
# This is the cleanest Bruhat-style test before adding torus parts
# to t.
############################################################

println("============================================================")
println("PURE WEYL BRUHAT-TYPE t SEARCH")
println("============================================================")

############################################################
# Hybrid trace function
############################################################

function RootExponentModN(r_e, vec, n)
    r_simple = F4ToSimpleCoefficients(r_e)

    expo = 0
    for j in 1:4
        expo += r_simple[j] * vec[j]
    end

    return mod(expo, n)
end

function Hybrid_AdjointTrace(x)
    u, a, w = x

    cartan_trace = IntFromQ(MatTraceQ(w))
    zsum = complex(float(cartan_trace), 0.0)

    for r in F4_ROOTS_E_FOR_W
        img = MatApplyQ(w, r)

        if img == r
            expo13 = RootExponentModN(r, u, 13)
            expo6  = RootExponentModN(r, a, 6)

            zsum += cis(2*pi*expo13/13) * cis(2*pi*expo6/6)
        end
    end

    return round(Int, real(zsum))
end

############################################################
# Weyl-level helper functions
############################################################

function WeylConjugate(v, w)
    return MatMulQ(MatMulQ(v, w), MatTransposeQ(v))
end

function WeylEqual(A, B)
    return MatKeyQ(A) == MatKeyQ(B)
end

function WeylNormalisesG13(w, gvec)
    return WeylActionExponentOnG13(w, gvec) != 0
end

function HybridNormalisesG13(t, g)
    conj = Hybrid_Conjugate(t, g)

    for k in 0:12
        if Hybrid_Key(conj) == Hybrid_Key(Hybrid_Pow(g, k))
            return true
        end
    end

    return false
end

############################################################
# Data from the corrected f
############################################################

f_w = f_w_corrected
f_w_inv = MatTransposeQ(f_w)

zero13 = [0,0,0,0]
zero6 = [0,0,0,0]

println("Corrected f Weyl order = ", MatOrderQ(f_w))
println("Corrected f Weyl action on g = ", WeylActionExponentOnG13(f_w, g13_vec))
println("B_hybrid size = ", length(B_hybrid))

############################################################
# Search pure Weyl t candidates
############################################################

pure_weyl_t_candidates = []

for w in W_F4
    t_hybrid = (zero13, zero6, w)

    order_t = Hybrid_Order(t_hybrid)
    trace_t = Hybrid_AdjointTrace(t_hybrid)

    if order_t != 2
        continue
    end

    if trace_t != -4
        continue
    end

    # Walton-style inversion condition
    conj_f_w = WeylConjugate(w, f_w)
    inverts_f_weyl = WeylEqual(conj_f_w, f_w_inv)

    if !inverts_f_weyl
        continue
    end

    # PSL2 Bruhat t should move g outside <g>
    normalises_g = HybridNormalisesG13(t_hybrid, g_hybrid)

    # Search b in B such that order(b*t)=3
    order3_hits = []

    for bi in 1:length(B_hybrid)
        b = B_hybrid[bi]
        bt = Hybrid_Mul(b, t_hybrid)

        if Hybrid_Order(bt) == 3
            push!(order3_hits, bi)
        end
    end

    if length(order3_hits) > 0
        push!(pure_weyl_t_candidates,
              (w, order_t, trace_t, inverts_f_weyl, normalises_g, order3_hits))
    end
end

println("------------------------------------------------------------")
println("Pure Weyl t candidates")
println("------------------------------------------------------------")

println("Number of pure Weyl t candidates = ", length(pure_weyl_t_candidates))

for i in 1:length(pure_weyl_t_candidates)
    w, order_t, trace_t, inverts_f_weyl, normalises_g, order3_hits = pure_weyl_t_candidates[i]

    println("Candidate ", i)
    println("  order(t) = ", order_t)
    println("  trace(t) = ", trace_t)
    println("  t inverts f Weyl part? ", inverts_f_weyl)
    println("  t normalises <g>? ", normalises_g)
    println("  number of b in B with order(b*t)=3 = ", length(order3_hits))
    println("  first 20 b-indices = ", order3_hits[1:min(20,length(order3_hits))])
    println("  t Weyl action = ", SimpleRootImageData(w))
    println("------------------------------------------------------------")
end

############################################################
# Store first candidate if it exists
############################################################

if length(pure_weyl_t_candidates) > 0
    t_weyl_1 = pure_weyl_t_candidates[1][1]
    t_hybrid_1 = (zero13, zero6, t_weyl_1)

    println("Stored first pure Weyl t candidate as t_hybrid_1.")
    println("order(t_hybrid_1) = ", Hybrid_Order(t_hybrid_1))
    println("trace(t_hybrid_1) = ", Hybrid_AdjointTrace(t_hybrid_1))
else
    println("No pure Weyl t candidate found.")
    println("Then the next step is to allow torus parts in t.")
end

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")

println("This tests the cleanest Walton-style possibility first.")
println("If a candidate appears, then we can test <g,f,t> in the hybrid model.")
println("If no candidate appears, we must search t = (u,a,w) with non-trivial torus parts.")

println("============================================================")
println("END PURE WEYL BRUHAT-TYPE t SEARCH")
println("============================================================")

############################################################
# NEXT STEP:
# Search for Bruhat-type t with torus parts
#
# We now search:
#
#   t = (u, a, w)
#
# where:
#   u is mod 13 torus part,
#   a is mod 6 torus part,
#   w is a Weyl element.
#
# Conditions:
#
#   order(t) = 2
#   trace(t) = -4
#   t*f*t^{-1} = f^{-1}
#   there exists b in B = <g,f> such that order(b*t) = 3
#
# This is the next Walton-style step after pure Weyl t failed.
############################################################

println("============================================================")
println("BRUHAT-TYPE t SEARCH WITH TORUS PARTS")
println("============================================================")

############################################################
# Helper functions
############################################################

function VecKeyModN(v, n)
    return Tuple([mod(x,n) for x in v])
end

function VecZeroModN(v, n)
    return all(x -> mod(x,n) == 0, v)
end

function VecAddModN(v, w, n)
    return [mod(v[i] + w[i], n) for i in 1:length(v)]
end

function VecSubModN(v, w, n)
    return [mod(v[i] - w[i], n) for i in 1:length(v)]
end

function VectorFixedByWeyl(w, v, n)
    return VecKeyModN(WeylActionOnTorusVector(w, v, n), n) == VecKeyModN(v, n)
end

function VectorAntiFixedByWeyl(w, v, n)
    wv = WeylActionOnTorusVector(w, v, n)
    return VecZeroModN(VecAddModN(v, wv, n), n)
end

function VectorFixedByFInverse(v, n)
    return VectorFixedByWeyl(f_w_inv, v, n)
end

function Hybrid_ElementOrder3Hits(t_hybrid)
    hits = []

    for bi in 1:length(B_hybrid)
        b = B_hybrid[bi]
        bt = Hybrid_Mul(b, t_hybrid)

        if Hybrid_Order(bt) == 3
            push!(hits, bi)
        end
    end

    return hits
end

############################################################
# Generate all vectors mod 13
############################################################

vectors_13 = []

for x1 in 0:12
    for x2 in 0:12
        for x3 in 0:12
            for x4 in 0:12
                push!(vectors_13, [x1,x2,x3,x4])
            end
        end
    end
end

println("Number of mod-13 torus vectors = ", length(vectors_13))
println("Expected = 13^4 = 28561")

############################################################
# First find Weyl elements w which invert f_w
############################################################

weyl_inverting_f = []

for w in W_F4
    if MatOrderQ(w) != 2
        continue
    end

    conj_f_w = WeylConjugate(w, f_w)

    if WeylEqual(conj_f_w, f_w_inv)
        push!(weyl_inverting_f, w)
    end
end

println("Number of order-2 Weyl elements with w*f*w^{-1}=f^{-1}: ",
        length(weyl_inverting_f))

println("------------------------------------------------------------")
println("Weyl inverters of corrected f")
println("------------------------------------------------------------")

for i in 1:length(weyl_inverting_f)
    w = weyl_inverting_f[i]
    println("Weyl inverter ", i)
    println("  Weyl trace = ", IntFromQ(MatTraceQ(w)))
    println("  pure Weyl adjoint trace = ", Hybrid_AdjointTrace(([0,0,0,0], [0,0,0,0], w)))
    println("  normalises <g>? ", WeylNormalisesG13(w, g13_vec))
    println("  action on simple roots = ", SimpleRootImageData(w))
    println("------------------------------------------------------------")
end

############################################################
# Search t = (u,a,w)
#
# If w*f*w^{-1}=f^{-1}, then for full inversion
#
#   t*f*t^{-1} = f^{-1}
#
# the torus vector x=(u,a) must satisfy:
#
#   x is fixed by f^{-1}
#
# Also order(t)=2 requires:
#
#   x + w(x) = 0
#
# We impose these linear conditions first.
############################################################

bruhat_t_candidates = []
candidate_count_before_order3 = 0

for wi in 1:length(weyl_inverting_f)
    w = weyl_inverting_f[wi]

    println("Processing Weyl inverter ", wi, " of ", length(weyl_inverting_f))

    allowed_u = []

    for u in vectors_13
        if VectorAntiFixedByWeyl(w, u, 13) && VectorFixedByFInverse(u, 13)
            push!(allowed_u, u)
        end
    end

    allowed_a = []

    for a in torus_vectors_6
        if VectorAntiFixedByWeyl(w, a, 6) && VectorFixedByFInverse(a, 6)
            push!(allowed_a, a)
        end
    end

    println("  allowed u vectors mod 13 = ", length(allowed_u))
    println("  allowed a vectors mod 6  = ", length(allowed_a))
    println("  product count = ", length(allowed_u) * length(allowed_a))

    local_trace_minus4 = 0
    local_order3 = 0

    for u in allowed_u
        for a in allowed_a
            t_hybrid = (u, a, w)

            order_t = Hybrid_Order(t_hybrid)

            if order_t != 2
                continue
            end

            trace_t = Hybrid_AdjointTrace(t_hybrid)

            if trace_t != -4
                continue
            end

            candidate_count_before_order3 += 1
            local_trace_minus4 += 1

            order3_hits = Hybrid_ElementOrder3Hits(t_hybrid)

            if length(order3_hits) > 0
                local_order3 += 1

                normalises_g = HybridNormalisesG13(t_hybrid, g_hybrid)

                push!(bruhat_t_candidates,
                      (u, a, wi, w, trace_t, normalises_g, order3_hits))
            end
        end
    end

    println("  order-2 trace-minus-4 candidates for this w = ", local_trace_minus4)
    println("  candidates also satisfying order(b*t)=3 = ", local_order3)
    println("------------------------------------------------------------")
end

############################################################
# Print results
############################################################

println("============================================================")
println("BRUHAT-TYPE t SEARCH RESULTS")
println("============================================================")

println("Total order-2 trace-minus-4 candidates before order-3 test = ",
        candidate_count_before_order3)

println("Total Bruhat-type t candidates after order-3 test = ",
        length(bruhat_t_candidates))

for i in 1:min(30, length(bruhat_t_candidates))
    u, a, wi, w, trace_t, normalises_g, order3_hits = bruhat_t_candidates[i]

    println("Candidate ", i)
    println("  u mod 13 = ", u)
    println("  a mod 6  = ", a)
    println("  Weyl inverter index = ", wi)
    println("  order(t) = ", Hybrid_Order((u,a,w)))
    println("  trace(t) = ", trace_t)
    println("  t normalises <g>? ", normalises_g)
    println("  number of b in B with order(b*t)=3 = ", length(order3_hits))
    println("  first 20 b-indices = ", order3_hits[1:min(20,length(order3_hits))])
    println("  Weyl action = ", SimpleRootImageData(w))
    println("------------------------------------------------------------")
end

############################################################
# Store first candidate
############################################################

if length(bruhat_t_candidates) > 0
    u_t_1, a_t_1, wi_t_1, w_t_1, trace_t_1, normalises_g_1, order3_hits_1 =
        bruhat_t_candidates[1]

    t_hybrid_1 = (u_t_1, a_t_1, w_t_1)

    println("Stored first Bruhat-type candidate as t_hybrid_1.")
    println("order(t_hybrid_1) = ", Hybrid_Order(t_hybrid_1))
    println("trace(t_hybrid_1) = ", Hybrid_AdjointTrace(t_hybrid_1))
    println("first order-3 b-index = ", order3_hits_1[1])
else
    println("No Bruhat-type t found in this hybrid torus-normaliser model.")
    println("Then the next step is outside this hybrid model, probably genuine F4(7).")
end

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")
println("This is the full torus-part version of the local Walton t-search inside")
println("the hybrid torus-normaliser model.")
println("If this produces candidates, next we test <g,f,t>.")
println("If this produces no candidates, the hybrid model is too small and the next step")
println("must move to a genuine F4(7) construction or another faithful module model.")

println("============================================================")
println("END BRUHAT-TYPE t SEARCH WITH TORUS PARTS")
println("============================================================")

############################################################
# NEXT STEP:
# Search over ALL corrected f-candidates and all torus-part t's
#
# Previous result:
#
#   f with torus vector [0,0,0,0] gave no Bruhat t.
#
# But the normalising f search produced 1296 candidates:
#
#   f = (0, a_f, f_w)
#
# all with:
#   order(f) = 6
#   f*g*f^{-1} = g^10
#   trace profile [2,-2,-4]
#
# So now we vary a_f and search again for:
#
#   t = (u_t, a_t, w_t)
#
# satisfying:
#
#   order(t) = 2
#   trace(t) = -4
#   t*f*t^{-1} = f^{-1}
#   exists b in B=<g,f> with order(b*t)=3
############################################################

println("============================================================")
println("SEARCH ALL corrected f-CANDIDATES FOR BRUHAT t")
println("============================================================")

############################################################
# Exact hybrid equality
############################################################

function Hybrid_Equal(x, y)
    return Hybrid_Key(x) == Hybrid_Key(y)
end

############################################################
# Precompute Weyl inverters of the corrected f Weyl part
############################################################

if !isdefined(Main, :weyl_inverting_f)
    weyl_inverting_f = []

    for w in W_F4
        if MatOrderQ(w) != 2
            continue
        end

        conj_f_w = WeylConjugate(w, f_w_corrected)

        if WeylEqual(conj_f_w, f_w_inv)
            push!(weyl_inverting_f, w)
        end
    end
end

println("Number of Weyl inverters of f_w = ", length(weyl_inverting_f))

############################################################
# Precompute possible t-vectors for each Weyl inverter
#
# Conditions independent of f_a:
#
#   order(t)=2
#   trace(t)=-4
#
# We first search t=(u,a,w), but from the previous linear condition
# the allowed u-space was only zero for each inverter. Still, we keep
# the general loop for safety.
############################################################

println("------------------------------------------------------------")
println("Precomputing t candidates by Weyl inverter")
println("------------------------------------------------------------")

precomputed_t_by_wi = Dict{Int, Any}()

for wi in 1:length(weyl_inverting_f)
    w = weyl_inverting_f[wi]

    allowed_u = []

    for u in vectors_13
        if VectorAntiFixedByWeyl(w, u, 13) && VectorFixedByFInverse(u, 13)
            push!(allowed_u, u)
        end
    end

    possible_t_for_w = []

    for u in allowed_u
        for a in torus_vectors_6
            t_hybrid = (u, a, w)

            if Hybrid_Order(t_hybrid) != 2
                continue
            end

            if Hybrid_AdjointTrace(t_hybrid) != -4
                continue
            end

            push!(possible_t_for_w, t_hybrid)
        end
    end

    precomputed_t_by_wi[wi] = possible_t_for_w

    println("Weyl inverter ", wi)
    println("  allowed u count = ", length(allowed_u))
    println("  order-2 trace-minus-4 t count = ", length(possible_t_for_w))
end

total_precomputed_t = sum(length(precomputed_t_by_wi[wi]) for wi in 1:length(weyl_inverting_f))

println("Total precomputed t candidates before matching f_a = ", total_precomputed_t)

############################################################
# Search over all f-candidates
############################################################

all_f_t_bruhat_candidates = []

println("------------------------------------------------------------")
println("Searching over all corrected f-candidates")
println("------------------------------------------------------------")

for fi in 1:length(normalising_f_candidates)
    f_a, f_wi, f_w, f_prof = normalising_f_candidates[fi]

    f_current = (zero13, f_a, f_w)
    f_current_inv = Hybrid_Inverse(f_current)

    # Basic safety checks
    if Hybrid_Order(f_current) != 6
        continue
    end

    if !Hybrid_Equal(Hybrid_Conjugate(f_current, g_hybrid), Hybrid_Pow(g_hybrid, 10))
        continue
    end

    local_inverting_t_count = 0
    local_order3_count = 0

    B_current = nothing
    B_current_built = false

    for wi in 1:length(weyl_inverting_f)
        possible_t_for_w = precomputed_t_by_wi[wi]

        if length(possible_t_for_w) == 0
            continue
        end

        for t_hybrid in possible_t_for_w

            # Exact full inversion test:
            #   t*f*t^{-1} = f^{-1}
            if !Hybrid_Equal(Hybrid_Conjugate(t_hybrid, f_current), f_current_inv)
                continue
            end

            local_inverting_t_count += 1

            # Build B=<g,f> only when needed
            if !B_current_built
                B_current = Hybrid_GroupGeneratedBy([g_hybrid, f_current])
                B_current_built = true
            end

            # Check B size
            if length(B_current) != 78
                continue
            end

            order3_hits = []

            for bi in 1:length(B_current)
                b = B_current[bi]
                bt = Hybrid_Mul(b, t_hybrid)

                if Hybrid_Order(bt) == 3
                    push!(order3_hits, bi)
                end
            end

            if length(order3_hits) > 0
                local_order3_count += 1

                normalises_g = HybridNormalisesG13(t_hybrid, g_hybrid)

                push!(all_f_t_bruhat_candidates,
                      (fi, f_a, t_hybrid, wi, normalises_g, order3_hits))
            end
        end
    end

    if local_inverting_t_count > 0 || local_order3_count > 0
        println("f candidate ", fi)
        println("  f_a = ", f_a)
        println("  inverting t count = ", local_inverting_t_count)
        println("  Bruhat order-3 t count = ", local_order3_count)
        if B_current_built
            println("  |<g,f>| = ", length(B_current))
        end
        println("------------------------------------------------------------")
    end

    if fi % 100 == 0
        println("Processed f candidates: ", fi, " / ", length(normalising_f_candidates),
                " | total Bruhat candidates so far = ", length(all_f_t_bruhat_candidates))
    end
end

############################################################
# Print final results
############################################################

println("============================================================")
println("ALL corrected f-CANDIDATE SEARCH RESULTS")
println("============================================================")

println("Total Bruhat candidates found = ", length(all_f_t_bruhat_candidates))

for i in 1:min(30, length(all_f_t_bruhat_candidates))
    fi, f_a, t_hybrid, wi, normalises_g, order3_hits = all_f_t_bruhat_candidates[i]
    u_t, a_t, w_t = t_hybrid

    println("Candidate ", i)
    println("  f candidate index = ", fi)
    println("  f torus vector a_f = ", f_a)
    println("  t u mod 13 = ", u_t)
    println("  t a mod 6  = ", a_t)
    println("  t Weyl inverter index = ", wi)
    println("  order(t) = ", Hybrid_Order(t_hybrid))
    println("  trace(t) = ", Hybrid_AdjointTrace(t_hybrid))
    println("  t normalises <g>? ", normalises_g)
    println("  number of b in B with order(b*t)=3 = ", length(order3_hits))
    println("  first 20 b-indices = ", order3_hits[1:min(20,length(order3_hits))])
    println("  t Weyl action = ", SimpleRootImageData(w_t))
    println("------------------------------------------------------------")
end

############################################################
# Store first full candidate if found
############################################################

if length(all_f_t_bruhat_candidates) > 0
    fi_1, f_a_final_1, t_hybrid_final_1, wi_final_1, normalises_g_final_1, order3_hits_final_1 =
        all_f_t_bruhat_candidates[1]

    f_hybrid_final_1 = (zero13, f_a_final_1, f_w_corrected)

    println("Stored first full candidate:")
    println("  f_hybrid_final_1")
    println("  t_hybrid_final_1")
    println("  first order-3 b-index = ", order3_hits_final_1[1])

    println("Checking final stored candidate:")
    println("  order(g) = ", Hybrid_Order(g_hybrid))
    println("  order(f) = ", Hybrid_Order(f_hybrid_final_1))
    println("  order(t) = ", Hybrid_Order(t_hybrid_final_1))
    println("  trace(t) = ", Hybrid_AdjointTrace(t_hybrid_final_1))
    println("  |<g,f>| = ", length(Hybrid_GroupGeneratedBy([g_hybrid, f_hybrid_final_1])))
else
    println("No Bruhat t found for any of the 1296 corrected f-candidates.")
    println("This strongly suggests the hybrid torus-normaliser model is too small.")
    println("The next step would be a genuine F4(7) construction or a faithful module model.")
end

println("============================================================")
println("END ALL corrected f-CANDIDATE SEARCH")
println("============================================================")

############################################################
# CORRECTED NEXT STEP:
# Search all corrected f-candidates again, but do NOT impose
# the wrong fixed-vector condition on the mod-6 torus part of t.
#
# Previous mistake:
#
#   VectorFixedByFInverse(a,6)
#
# is only valid when f has torus vector 0.
#
# For general f = (0, f_a, f_w), we must test directly:
#
#   t*f*t^{-1} = f^{-1}
#
# using Hybrid_Conjugate.
############################################################

println("============================================================")
println("CORRECTED ALL-f BRUHAT t SEARCH")
println("============================================================")

############################################################
# Exact hybrid equality
############################################################

function Hybrid_Equal(x, y)
    return Hybrid_Key(x) == Hybrid_Key(y)
end

############################################################
# First compute the u-vectors allowed by the order-13 part.
#
# For t=(u,a,w), f=(0,f_a,f_w), and w*f_w*w^{-1}=f_w^{-1},
# the order-13 part of t*f*t^{-1}=f^{-1} forces:
#
#   u fixed by f_w^{-1}
#
# Also order(t)=2 forces:
#
#   u + w(u) = 0.
#
# This part is independent of f_a.
############################################################

println("------------------------------------------------------------")
println("Precomputing allowed u-vectors for each Weyl inverter")
println("------------------------------------------------------------")

allowed_u_by_wi = Dict{Int, Any}()

for wi in 1:length(weyl_inverting_f)
    w = weyl_inverting_f[wi]

    allowed_u = []

    for u in vectors_13
        if VectorAntiFixedByWeyl(w, u, 13) && VectorFixedByFInverse(u, 13)
            push!(allowed_u, u)
        end
    end

    allowed_u_by_wi[wi] = allowed_u

    println("Weyl inverter ", wi, " allowed u count = ", length(allowed_u))
end

############################################################
# For mod-6 torus part a_t, we only impose order(t)=2 first:
#
#   a_t + w(a_t) = 0.
#
# Then for each f_a we test exact conjugation directly.
############################################################

println("------------------------------------------------------------")
println("Precomputing anti-fixed mod-6 torus vectors for each Weyl inverter")
println("------------------------------------------------------------")

anti_a_by_wi = Dict{Int, Any}()

for wi in 1:length(weyl_inverting_f)
    w = weyl_inverting_f[wi]

    anti_a = []

    for a in torus_vectors_6
        if VectorAntiFixedByWeyl(w, a, 6)
            push!(anti_a, a)
        end
    end

    anti_a_by_wi[wi] = anti_a

    println("Weyl inverter ", wi, " anti-fixed a count = ", length(anti_a))
end

############################################################
# Main corrected search
############################################################

corrected_all_f_t_candidates = []

println("------------------------------------------------------------")
println("Searching all corrected f-candidates")
println("------------------------------------------------------------")

for fi in 1:length(normalising_f_candidates)
    f_a, f_wi, f_w, f_prof = normalising_f_candidates[fi]

    f_current = (zero13, f_a, f_w)
    f_current_inv = Hybrid_Inverse(f_current)

    # safety checks
    if Hybrid_Order(f_current) != 6
        continue
    end

    if !Hybrid_Equal(Hybrid_Conjugate(f_current, g_hybrid), Hybrid_Pow(g_hybrid, 10))
        continue
    end

    B_current = nothing
    B_current_built = false

    local_exact_inverters = 0
    local_trace_minus4 = 0
    local_bruhat = 0

    for wi in 1:length(weyl_inverting_f)
        w = weyl_inverting_f[wi]

        allowed_u = allowed_u_by_wi[wi]
        anti_a = anti_a_by_wi[wi]

        if length(allowed_u) == 0 || length(anti_a) == 0
            continue
        end

        for u in allowed_u
            for a_t in anti_a
                t_hybrid = (u, a_t, w)

                # order(t)=2 should already mostly follow from anti-fixed conditions,
                # but keep exact check.
                if Hybrid_Order(t_hybrid) != 2
                    continue
                end

                # exact full inversion test
                if !Hybrid_Equal(Hybrid_Conjugate(t_hybrid, f_current), f_current_inv)
                    continue
                end

                local_exact_inverters += 1

                trace_t = Hybrid_AdjointTrace(t_hybrid)

                if trace_t != -4
                    continue
                end

                local_trace_minus4 += 1

                # Build B only now
                if !B_current_built
                    B_current = Hybrid_GroupGeneratedBy([g_hybrid, f_current])
                    B_current_built = true
                end

                if length(B_current) != 78
                    continue
                end

                order3_hits = []

                for bi in 1:length(B_current)
                    b = B_current[bi]
                    bt = Hybrid_Mul(b, t_hybrid)

                    if Hybrid_Order(bt) == 3
                        push!(order3_hits, bi)
                    end
                end

                if length(order3_hits) > 0
                    local_bruhat += 1

                    normalises_g = HybridNormalisesG13(t_hybrid, g_hybrid)

                    push!(corrected_all_f_t_candidates,
                          (fi, f_a, t_hybrid, wi, trace_t, normalises_g, order3_hits))
                end
            end
        end
    end

    if local_exact_inverters > 0 || local_trace_minus4 > 0 || local_bruhat > 0
        println("f candidate ", fi)
        println("  f_a = ", f_a)
        println("  exact inverting t count = ", local_exact_inverters)
        println("  exact inverting and trace-minus-4 count = ", local_trace_minus4)
        println("  Bruhat order-3 count = ", local_bruhat)
        if B_current_built
            println("  |<g,f>| = ", length(B_current))
        end
        println("------------------------------------------------------------")
    end

    if fi % 100 == 0
        println("Processed f candidates: ", fi, " / ", length(normalising_f_candidates),
                " | total Bruhat candidates so far = ", length(corrected_all_f_t_candidates))
    end
end

############################################################
# Print final results
############################################################

println("============================================================")
println("CORRECTED ALL-f BRUHAT t SEARCH RESULTS")
println("============================================================")

println("Total corrected Bruhat candidates found = ",
        length(corrected_all_f_t_candidates))

for i in 1:min(30, length(corrected_all_f_t_candidates))
    fi, f_a, t_hybrid, wi, trace_t, normalises_g, order3_hits =
        corrected_all_f_t_candidates[i]

    u_t, a_t, w_t = t_hybrid

    println("Candidate ", i)
    println("  f candidate index = ", fi)
    println("  f torus vector a_f = ", f_a)
    println("  t u mod 13 = ", u_t)
    println("  t a mod 6  = ", a_t)
    println("  t Weyl inverter index = ", wi)
    println("  order(t) = ", Hybrid_Order(t_hybrid))
    println("  trace(t) = ", trace_t)
    println("  t normalises <g>? ", normalises_g)
    println("  number of b in B with order(b*t)=3 = ", length(order3_hits))
    println("  first 20 b-indices = ", order3_hits[1:min(20,length(order3_hits))])
    println("  t Weyl action = ", SimpleRootImageData(w_t))
    println("------------------------------------------------------------")
end

############################################################
# Store first full candidate if found
############################################################

if length(corrected_all_f_t_candidates) > 0
    fi_1, f_a_final_1, t_hybrid_final_1, wi_final_1, trace_t_final_1,
        normalises_g_final_1, order3_hits_final_1 =
        corrected_all_f_t_candidates[1]

    f_hybrid_final_1 = (zero13, f_a_final_1, f_w_corrected)

    println("Stored first corrected full candidate:")
    println("  f_hybrid_final_1")
    println("  t_hybrid_final_1")
    println("  first order-3 b-index = ", order3_hits_final_1[1])

    println("Checking final stored candidate:")
    println("  order(g) = ", Hybrid_Order(g_hybrid))
    println("  order(f) = ", Hybrid_Order(f_hybrid_final_1))
    println("  order(t) = ", Hybrid_Order(t_hybrid_final_1))
    println("  trace(t) = ", Hybrid_AdjointTrace(t_hybrid_final_1))
    println("  |<g,f>| = ", length(Hybrid_GroupGeneratedBy([g_hybrid, f_hybrid_final_1])))
else
    println("No corrected Bruhat t found.")
    println("This would be a stronger indication that the hybrid model is too small.")
end

println("============================================================")
println("END CORRECTED ALL-f BRUHAT t SEARCH")
println("============================================================")
