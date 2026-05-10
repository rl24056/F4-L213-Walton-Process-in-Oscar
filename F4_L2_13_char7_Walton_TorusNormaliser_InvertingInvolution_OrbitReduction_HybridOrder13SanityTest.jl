############################################################
# F4_L2_13_char7_Walton_TorusNormaliser_OrbitReduction_HybridSanityTest.jl
#
# Purpose:
#
# This script records the Walton-style characteristic-7 F4/L2(13)
# torus-normaliser calculations done so far.
#
# It does five things:
#
#   1. Builds the F4 root system and Weyl group W(F4).
#   2. Fixes the Walton-style order-6 element f with Kac tuple
#
#          kac_f = [0, 1, 0, 1, 1]
#
#      giving adjoint traces:
#
#          trace(f)   =  2
#          trace(f^2) = -2
#          trace(f^3) = -4
#
#   3. Searches the split torus-normaliser model over F7 for
#      order-2, trace-minus-4 elements t in the Weyl inverting coset.
#
#   4. Reduces the 1296 good t-candidates under the split centraliser
#
#          C_split(f) = T . W_cent(f)
#
#      obtaining 9 orbit representatives.
#
#   5. Checks the local f,t relation and then runs a hybrid
#      order-13/order-6 torus sanity test, showing why the real
#      order-13 element g must be introduced outside this same
#      split torus-normaliser model.
#
# Run in Julia/OSCAR:
#
#   using Oscar
#   include("F4_L2_13_char7_Walton_TorusNormaliser_OrbitReduction_HybridSanityTest.jl")
#
############################################################

println("============================================================")
println("F4(7) WALTON-STYLE TORUS-NORMALISER RESTART")
println("============================================================")

############################################################
# PART 1.
# F4 roots and basic root functions
############################################################

function F4RootListE()
    roots = Vector{Vector{Rational{Int}}}()

    # roots +/- e_i
    for i in 1:4
        for s in [-1, 1]
            v = [0//1, 0//1, 0//1, 0//1]
            v[i] = s//1
            push!(roots, v)
        end
    end

    # roots +/- e_i +/- e_j
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

    # half roots 1/2(+-e1 +-e2 +-e3 +-e4)
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

println("Number of F4 roots = ", length(F4_ROOT_COEFFS))

############################################################
# PART 2.
# Matrix functions for Weyl group
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
# PART 3.
# Build W(F4)
############################################################

F4_SIMPLE_ROOTS_E = [
    [0//1, 1//1, -1//1, 0//1],
    [0//1, 0//1, 1//1, -1//1],
    [0//1, 0//1, 0//1, 1//1],
    [1//2, -1//2, -1//2, -1//2]
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

############################################################
# PART 4.
# Fix the Walton-style order-6 element f
#
# From previous calculation:
#
#   kac_f = [0,1,0,1,1]
#
# This gives:
#   trace(f)   =  2
#   trace(f^2) = -2
#   trace(f^3) = -4
#
# and zero-root subsystem A1 + A1.
############################################################

kac_f = [0, 1, 0, 1, 1]
n_f = 6

function F4KacExponentE(v, kac, n)
    r = F4ToSimpleCoefficients(v)
    return mod(r[1]*kac[1] + r[2]*kac[2] + r[3]*kac[3] + r[4]*kac[4], n)
end

function WeylCentralisesKac(M, kac, n)
    for r in F4_ROOTS_E_FOR_W
        lhs = F4KacExponentE(MatApplyQ(M, r), kac, n)
        rhs = F4KacExponentE(r, kac, n)

        if lhs != rhs
            return false
        end
    end

    return true
end

function WeylInvertsKac(M, kac, n)
    for r in F4_ROOTS_E_FOR_W
        lhs = F4KacExponentE(MatApplyQ(M, r), kac, n)
        rhs = mod(-F4KacExponentE(r, kac, n), n)

        if lhs != rhs
            return false
        end
    end

    return true
end

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
println("Weyl-level data for f")
println("------------------------------------------------------------")
println("Kac tuple for f = ", kac_f)
println("Size of W_cent(f) = ", length(W_cent_f))
println("Size of W_inv(f)  = ", length(W_inv_f))
println("Orders in W_inv(f) = ", sort([MatOrderQ(M) for M in W_inv_f]))

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
# PART 5.
# Split torus-normaliser model over F7
#
# Since q = 7, F7^* has order 6.
# Torus elements are exponent vectors in (Z/6Z)^4.
############################################################

println("============================================================")
println("SPLIT TORUS-NORMALISER MODEL OVER F7")
println("============================================================")

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

function TW_Order(a, w, n; limit = 100)
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

############################################################
# Enumerate all torus vectors in (Z/6Z)^4
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

println("Number of split torus vectors = ", length(torus_vectors_6))
println("Expected = 6^4 = 1296")

############################################################
# Search in inverting coset
############################################################

println("------------------------------------------------------------")
println("Searching elements (a,w) with w in W_inv(f)")
println("Conditions: order 2 and adjoint trace -4")
println("------------------------------------------------------------")

good_TW_t = []
trace_distribution = Dict{Int, Int}()
order_distribution = Dict{Int, Int}()

for wi in 1:length(W_inv_f)
    w = W_inv_f[wi]

    local_count_order2 = 0
    local_count_trace_minus4 = 0

    for a in torus_vectors_6
        ord = TW_Order(a, w, n_torus)
        tr = TW_AdjointTrace(a, w, n_torus)

        order_distribution[ord] = get(order_distribution, ord, 0) + 1
        trace_distribution[tr] = get(trace_distribution, tr, 0) + 1

        if ord == 2
            local_count_order2 += 1
        end

        if ord == 2 && tr == -4
            local_count_trace_minus4 += 1
            push!(good_TW_t, (a, wi, w, tr))
        end
    end

    println("W_inv element ", wi)
    println("  Weyl order = ", MatOrderQ(w))
    println("  order-2 elements (a,w) = ", local_count_order2)
    println("  order-2 and trace -4 elements = ", local_count_trace_minus4)
    println("  Weyl action on simple roots = ", SimpleRootImageData(w))
end

println("------------------------------------------------------------")
println("Global distributions")
println("------------------------------------------------------------")

println("Order distribution for all (a,w), w in W_inv(f):")
for k in sort(collect(keys(order_distribution)))
    println("  order ", k, ": ", order_distribution[k])
end

println("Trace distribution for all (a,w), w in W_inv(f):")
for k in sort(collect(keys(trace_distribution)))
    println("  trace ", k, ": ", trace_distribution[k])
end

println("------------------------------------------------------------")
println("Good candidates")
println("------------------------------------------------------------")

println("Total number of order-2 trace-minus-4 candidates = ", length(good_TW_t))

println("First 20 good candidates:")
println("  torus exponent vector a, Weyl inverting element index, trace")
println("------------------------------------------------------------")

for i in 1:min(20, length(good_TW_t))
    a, wi, w, tr = good_TW_t[i]
    println(i, ": a = ", a, ", W_inv index = ", wi, ", trace = ", tr)
end

############################################################
# PART 6.
# Orbit reduction of the 1296 good t-candidates
#
# We found:
#
#   good_TW_t has 1296 elements.
#
# These are all elements of the form:
#
#   (a, -I)
#
# with order 2 and trace -4.
#
# Now reduce them under conjugation by the split centraliser:
#
#   C_split(f) = T . W_cent(f)
#
# This is the analogue of Walton reducing the inverting
# involution search by centraliser/stabiliser orbits.
############################################################

println("============================================================")
println("ORBIT REDUCTION OF GOOD t-CANDIDATES")
println("============================================================")

############################################################
# Semidirect inverse and conjugation
############################################################

function TorusVectorNeg(a, n)
    return [mod(-a[i], n) for i in 1:length(a)]
end

function TW_Inverse(x, n)
    a, w = x

    winv = MatTransposeQ(w)
    minus_a = TorusVectorNeg(a, n)

    inv_a = WeylActionOnTorusVector(winv, minus_a, n)

    return (inv_a, winv)
end

function TW_Conjugate(s, x, n)
    return TW_Mul(TW_Mul(s, x, n), TW_Inverse(s, n), n)
end

function TW_Key(x, n)
    a, w = x
    return (Tuple([mod(ai, n) for ai in a]), MatKeyQ(w))
end

############################################################
# Build candidate dictionary from good_TW_t
############################################################

candidate_elems = []

for item in good_TW_t
    a, wi, w, tr = item
    push!(candidate_elems, ([mod(ai, n_torus) for ai in a], w))
end

candidate_dict = Dict{Any, Any}()

for x in candidate_elems
    candidate_dict[TW_Key(x, n_torus)] = x
end

println("Number of good candidates stored = ", length(candidate_dict))
println("Expected = 1296")

############################################################
# Build conjugating generators for C_split(f) = T . W_cent(f)
#
# Torus generators:
#   e1, e2, e3, e4 in (Z/6Z)^4
#
# Their conjugation action on (a,-I) shifts a by 2ei.
#
# Weyl centraliser elements:
#   use all elements of W_cent(f).
############################################################

centralizer_conjugators = []

# Torus generators
for i in 1:4
    b = [0,0,0,0]
    b[i] = 1
    push!(centralizer_conjugators, (b, I4Q))
end

# Weyl centraliser elements
for c in W_cent_f
    push!(centralizer_conjugators, ([0,0,0,0], c))
end

println("Number of centraliser conjugating generators = ", length(centralizer_conjugators))

############################################################
# Compute orbits
############################################################

remaining = Set(collect(keys(candidate_dict)))

orbits = []
orbit_reps = []

while !isempty(remaining)
    k0 = first(remaining)
    x0 = candidate_dict[k0]

    delete!(remaining, k0)

    orb_keys = Set([k0])
    queue = [x0]

    while !isempty(queue)
        x = popfirst!(queue)

        for s in centralizer_conjugators
            y = TW_Conjugate(s, x, n_torus)
            ky = TW_Key(y, n_torus)

            if haskey(candidate_dict, ky) && !(ky in orb_keys)
                push!(orb_keys, ky)
                push!(queue, y)

                if ky in remaining
                    delete!(remaining, ky)
                end
            end
        end
    end

    push!(orbits, orb_keys)
    push!(orbit_reps, x0)
end

println("------------------------------------------------------------")
println("Orbit reduction result")
println("------------------------------------------------------------")

println("Number of orbits = ", length(orbits))
println("Orbit sizes = ", sort([length(o) for o in orbits]))

############################################################
# Print representatives
############################################################

orbit_data = []

for i in 1:length(orbits)
    push!(orbit_data, (length(orbits[i]), orbit_reps[i], orbits[i]))
end

sort!(orbit_data, by = x -> x[1])

println("------------------------------------------------------------")
println("Orbit representatives")
println("------------------------------------------------------------")

for i in 1:length(orbit_data)
    sz, rep, orb = orbit_data[i]
    a, w = rep

    println("Orbit ", i)
    println("  size = ", sz)
    println("  representative a = ", a)
    println("  parity a mod 2 = ", [mod(ai,2) for ai in a])
    println("  order = ", TW_Order(a, w, n_torus))
    println("  trace = ", TW_AdjointTrace(a, w, n_torus))
    println("  Weyl action = ", SimpleRootImageData(w))
    println("------------------------------------------------------------")
end

############################################################
# Check that every orbit representative still has the right data
############################################################

println("Checking representatives:")

for i in 1:length(orbit_data)
    sz, rep, orb = orbit_data[i]
    a, w = rep

    ok_order = TW_Order(a, w, n_torus) == 2
    ok_trace = TW_AdjointTrace(a, w, n_torus) == -4
    ok_inverts = WeylInvertsKac(w, kac_f, n_f)

    println("Orbit ", i,
            " | order ok = ", ok_order,
            " | trace ok = ", ok_trace,
            " | Weyl inverts f = ", ok_inverts)
end

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")
println("The 1296 order-2 trace-minus-4 candidates have now been")
println("reduced to orbit representatives under C_split(f) = T . W_cent(f).")
println("These representatives are the next small list to test against")
println("the PSL2(13) Bruhat/order-3 condition.")

############################################################
# PART 7.
# Abstract PSL2(13) Bruhat and vector-space test over GF(7)
#
# This is not yet inside F4(7).
# This checks the Walton-style PSL2(13) blueprint:
#
#   g has order 13
#   f has order 6
#   B = <g,f> has order 78
#   t has order 2
#   <g,f,t> has order 1092
#   some b*t has order 3
#
# Then we test the permutation-module span:
#
#   v, v^t, (v^t)^g, ..., (v^t)^(g^12)
#
# on the 14-point action of PSL2(13).
############################################################

println("============================================================")
println("ABSTRACT PSL2(13) BRUHAT / VECTOR TEST OVER GF(7)")
println("============================================================")

############################################################
# Points of P^1(F13)
#
# We represent:
#   0,1,...,12 as finite field points
#   13 as infinity
############################################################

P13_POINTS = collect(0:13)
INF13 = 13

function PointIndex13(x)
    if x == INF13
        return 14
    else
        return x + 1
    end
end

function IndexPoint13(i)
    if i == 14
        return INF13
    else
        return i - 1
    end
end

function InvModPrime(a, p)
    a = mod(a, p)

    if a == 0
        error("Tried to invert 0 modulo prime.")
    end

    for x in 1:p-1
        if mod(a*x, p) == 1
            return x
        end
    end

    error("No inverse found.")
end

############################################################
# Mobius action of matrix [a b; c d] on P^1(F13)
############################################################

function MobiusPoint13(M, x)
    a, b, c, d = M
    p = 13

    a = mod(a,p)
    b = mod(b,p)
    c = mod(c,p)
    d = mod(d,p)

    if x == INF13
        if c == 0
            return INF13
        else
            return mod(a * InvModPrime(c,p), p)
        end
    else
        denom = mod(c*x + d, p)

        if denom == 0
            return INF13
        else
            return mod((a*x + b) * InvModPrime(denom,p), p)
        end
    end
end

function MobiusPerm13(M)
    perm = zeros(Int, 14)

    for x in P13_POINTS
        y = MobiusPoint13(M, x)
        perm[PointIndex13(x)] = PointIndex13(y)
    end

    return perm
end

############################################################
# Permutation functions
#
# PermMul(p,q) means apply p first, then q.
############################################################

function PermId(n)
    return collect(1:n)
end

function PermKey(p)
    return Tuple(p)
end

function PermMul(p, q)
    n = length(p)
    return [q[p[i]] for i in 1:n]
end

function PermInv(p)
    n = length(p)
    invp = zeros(Int, n)

    for i in 1:n
        invp[p[i]] = i
    end

    return invp
end

function PermPow(p, k)
    n = length(p)
    out = PermId(n)

    if k == 0
        return out
    end

    for i in 1:k
        out = PermMul(out, p)
    end

    return out
end

function PermOrder(p; limit = 5000)
    n = length(p)
    id = PermId(n)
    x = id

    for k in 1:limit
        x = PermMul(x, p)

        if x == id
            return k
        end
    end

    return 0
end

############################################################
# Generate group from permutations
############################################################

function PermGroupGeneratedBy(gens)
    seen = Dict{Any, Any}()
    queue = []

    id = PermId(length(gens[1]))

    seen[PermKey(id)] = id
    push!(queue, id)

    full_gens = copy(gens)

    for g in gens
        push!(full_gens, PermInv(g))
    end

    while !isempty(queue)
        x = popfirst!(queue)

        for s in full_gens
            y = PermMul(x, s)
            ky = PermKey(y)

            if !haskey(seen, ky)
                seen[ky] = y
                push!(queue, y)
            end
        end
    end

    return collect(values(seen))
end

############################################################
# Choose standard PSL2(13) generators
#
# g: x -> x + 1
# f: x -> 10x
# t: x -> -1/x
#
# f acts on <g> by exponent 10.
############################################################

M_g = (1, 1, 0, 1)
M_f = (6, 0, 0, 11)      # projectively x -> 10x
M_t = (0, 1, -1, 0)      # x -> -1/x

p_g = MobiusPerm13(M_g)
p_f = MobiusPerm13(M_f)
p_t = MobiusPerm13(M_t)

println("order(g) = ", PermOrder(p_g))
println("order(f) = ", PermOrder(p_f))
println("order(t) = ", PermOrder(p_t))

B_abs = PermGroupGeneratedBy([p_g, p_f])
H_abs = PermGroupGeneratedBy([p_g, p_f, p_t])

println("|<g,f>| = ", length(B_abs))
println("|<g,f,t>| = ", length(H_abs))
println("Expected |B| = 78")
println("Expected |PSL2(13)| = 1092")

############################################################
# Check whether f acts on <g> by exponent 10 or 4
############################################################

function FindActionExponentOnG(x, g)
    xinv = PermInv(x)
    conj = PermMul(PermMul(xinv, g), x)

    for k in 1:12
        if conj == PermPow(g,k)
            return k
        end
    end

    return 0
end

println("Action exponent of f on <g> = ", FindActionExponentOnG(p_f, p_g))

############################################################
# Bruhat/order-3 checks
############################################################

println("------------------------------------------------------------")
println("Order-3 Bruhat checks")
println("------------------------------------------------------------")

pure_g_order3 = []

for k in 0:12
    elem = PermMul(PermPow(p_g,k), p_t)
    ord = PermOrder(elem)

    if ord == 3
        push!(pure_g_order3, k)
    end
end

println("Pure g^k*t order-3 values k = ", pure_g_order3)

bt_order3 = []

for i in 0:12
    for j in 0:5
        b = PermMul(PermPow(p_g,i), PermPow(p_f,j))
        bt = PermMul(b, p_t)

        if PermOrder(bt) == 3
            push!(bt_order3, (i,j))
        end
    end
end

println("Number of pairs (i,j) with Order(g^i*f^j*t)=3 = ", length(bt_order3))
println("First 20 such pairs = ", bt_order3[1:min(20,length(bt_order3))])

############################################################
# GF(7) vector-space functions for permutation module
############################################################

function VecZero(n)
    return zeros(Int, n)
end

function VecBasis(n, i)
    v = zeros(Int, n)
    v[i] = 1
    return v
end

function VecAddMod(v, w, p)
    return [mod(v[i] + w[i], p) for i in 1:length(v)]
end

function VecSubMod(v, w, p)
    return [mod(v[i] - w[i], p) for i in 1:length(v)]
end

function PermActVectorRight(v, perm, p)
    n = length(v)
    out = zeros(Int, n)

    for i in 1:n
        out[perm[i]] = mod(out[perm[i]] + v[i], p)
    end

    return out
end

function RankModP(rows, p)
    if length(rows) == 0
        return 0
    end

    A = [copy([mod(x,p) for x in r]) for r in rows]
    m = length(A)
    n = length(A[1])

    rank = 0
    row = 1

    for col in 1:n
        pivot = 0

        for r in row:m
            if A[r][col] != 0
                pivot = r
                break
            end
        end

        if pivot == 0
            continue
        end

        A[row], A[pivot] = A[pivot], A[row]

        invpiv = InvModPrime(A[row][col], p)

        for c in col:n
            A[row][c] = mod(A[row][c] * invpiv, p)
        end

        for r in 1:m
            if r != row && A[r][col] != 0
                factor = A[r][col]

                for c in col:n
                    A[r][c] = mod(A[r][c] - factor*A[row][c], p)
                end
            end
        end

        rank += 1
        row += 1

        if row > m
            break
        end
    end

    return rank
end

############################################################
# B-fixed vector and Walton-style span
#
# B fixes infinity, so take:
#
#   v = e_infinity
#
# Then compute:
#
#   v, v^t, (v^t)^g, ..., (v^t)^(g^12)
############################################################

println("------------------------------------------------------------")
println("Walton-style vector span in the 14-point permutation module")
println("------------------------------------------------------------")

mod_char = 7

v_inf = VecBasis(14, PointIndex13(INF13))
v_t = PermActVectorRight(v_inf, p_t, mod_char)

span_vectors = []
push!(span_vectors, v_inf)

current = v_t

for k in 0:12
    if k == 0
        push!(span_vectors, v_t)
    else
        current = PermActVectorRight(current, p_g, mod_char)
        push!(span_vectors, current)
    end
end

println("Rank of span {v, v^t, (v^t)^g, ..., (v^t)^(g^12)} over GF(7) = ",
        RankModP(span_vectors, mod_char))

println("Expected rank in full 14-point permutation module = 14")

############################################################
# Augmentation and constant vector checks in characteristic 7
############################################################

const_vec = [1 for i in 1:14]
println("Sum of constant vector coordinates mod 7 = ", mod(sum(const_vec), 7))

augmentation_generators = []

for i in 1:13
    push!(augmentation_generators, VecSubMod(VecBasis(14,i), v_inf, mod_char))
end

println("Rank of augmentation subspace generators = ",
        RankModP(augmentation_generators, mod_char))

println("In characteristic 7, the constant vector lies inside augmentation because 14 = 0 mod 7.")

############################################################
# B-fixed space dimension on the 14-point permutation module
############################################################

function InvarianceEquationsForPerm(perm, n, p)
    rows = []

    for i in 1:n
        row = zeros(Int, n)
        row[perm[i]] = mod(row[perm[i]] + 1, p)
        row[i] = mod(row[i] - 1, p)
        push!(rows, row)
    end

    return rows
end

eqs = []
append!(eqs, InvarianceEquationsForPerm(p_g, 14, mod_char))
append!(eqs, InvarianceEquationsForPerm(p_f, 14, mod_char))

rank_eqs = RankModP(eqs, mod_char)
b_fixed_dim = 14 - rank_eqs

println("Dimension of B-fixed space on 14-point permutation module over GF(7) = ",
        b_fixed_dim)
println("Expected = 2, since B has two orbits: infinity and the 13 finite points.")

############################################################
# PART 8.
# Test the 9 torus-normaliser t orbit representatives
# against the local f,t relations.
#
# We have:
#   f represented by torus vector [s1,s2,s3,s4] = [0,1,0,1]
#   t representatives from orbit_data
#
# We test:
#   order(f) = 6
#   order(t) = 2
#   t*f*t^{-1} = f^{-1}
#   size <f,t>
#   order(f*t)
#
# This is the F4 torus-normaliser analogue of the PSL2(13)
# local relation before adding g.
############################################################

println("============================================================")
println("LOCAL f,t TEST FOR THE 9 TORUS-NORMALISER ORBIT REPS")
println("============================================================")

############################################################
# Group generation inside the finite semidirect product T.W
############################################################

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

function TW_GroupGeneratedBy(gens, n)
    seen = Dict{Any, Any}()
    queue = []

    id = ([0,0,0,0], I4Q)

    seen[TW_Key(id, n)] = id
    push!(queue, id)

    full_gens = copy(gens)

    for g in gens
        push!(full_gens, TW_Inverse(g, n))
    end

    while !isempty(queue)
        x = popfirst!(queue)

        for s in full_gens
            y = TW_Mul(x, s, n)
            ky = TW_Key(y, n)

            if !haskey(seen, ky)
                seen[ky] = y
                push!(queue, y)
            end
        end
    end

    return collect(values(seen))
end

function TW_Equal(x, y, n)
    return TW_Key(x, n) == TW_Key(y, n)
end

############################################################
# Define f as the torus element from the Kac tuple
############################################################

f_vec = [kac_f[1], kac_f[2], kac_f[3], kac_f[4]]
f_TW = (f_vec, I4Q)
f_inv_TW = TW_Inverse(f_TW, n_torus)

println("f torus vector = ", f_vec)
println("order(f) = ", TW_Order(f_vec, I4Q, n_torus))
println("trace(f)   = ", TW_AdjointTrace(f_vec, I4Q, n_torus))
println("trace(f^2) = ", TW_AdjointTrace(TW_Pow(f_TW,2,n_torus)[1],
                                      TW_Pow(f_TW,2,n_torus)[2],
                                      n_torus))
println("trace(f^3) = ", TW_AdjointTrace(TW_Pow(f_TW,3,n_torus)[1],
                                      TW_Pow(f_TW,3,n_torus)[2],
                                      n_torus))

println("------------------------------------------------------------")
println("Testing the 9 orbit representatives")
println("------------------------------------------------------------")

local_ft_data = []

for i in 1:length(orbit_data)
    sz, rep, orb = orbit_data[i]
    a_t, w_t = rep

    t_TW = (a_t, w_t)

    order_t = TW_Order(a_t, w_t, n_torus)
    trace_t = TW_AdjointTrace(a_t, w_t, n_torus)

    conj = TW_Conjugate(t_TW, f_TW, n_torus)
    inverts_f = TW_Equal(conj, f_inv_TW, n_torus)

    ft = TW_Mul(f_TW, t_TW, n_torus)
    order_ft = TW_Order(ft[1], ft[2], n_torus)

    subgroup_ft = TW_GroupGeneratedBy([f_TW, t_TW], n_torus)
    size_ft = length(subgroup_ft)

    push!(local_ft_data, (i, sz, a_t, order_t, trace_t, inverts_f, order_ft, size_ft))

    println("Orbit ", i)
    println("  orbit size = ", sz)
    println("  t torus vector a = ", a_t)
    println("  parity a mod 2 = ", [mod(x,2) for x in a_t])
    println("  order(t) = ", order_t)
    println("  trace(t) = ", trace_t)
    println("  t*f*t^{-1} = f^{-1}? ", inverts_f)
    println("  order(f*t) = ", order_ft)
    println("  size <f,t> = ", size_ft)
    println("------------------------------------------------------------")
end

############################################################
# Summary counts
############################################################

println("Summary table:")
println("orbit | orbit_size | a | order(t) | trace(t) | inverts f | order(f*t) | size<f,t>")

for row in local_ft_data
    i, sz, a_t, order_t, trace_t, inverts_f, order_ft, size_ft = row
    println(i, " | ", sz, " | ", a_t, " | ", order_t, " | ", trace_t,
            " | ", inverts_f, " | ", order_ft, " | ", size_ft)
end

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")
println("These nine representatives all have the correct order-2 and trace-minus-4 data.")
println("This step checks which of them also give the correct local dihedral relation with f.")
println("After this, the missing object is still g of order 13.")
println("The split torus-normaliser model cannot contain g, because F7^* has order 6.")
println("So the next serious F4 step must introduce the order-13 torus/class separately.")

############################################################
# PART 9.
# Hybrid order-13/order-6 torus sanity test
#
# Purpose:
#
# We now put the order-13 Kac representative
#
#   g Kac tuple = [1,1,1,1,2]
#
# into the same abstract torus model as f and t, only as a sanity test.
#
# This is NOT expected to produce PSL2(13), because in PSL2(13)
# the Bruhat involution t should move g outside its original 13-subgroup.
#
# We test:
#
#   trace(g) = 0
#   f centralises this naive g instead of acting by exponent 10
#   no g^k*t has order 3
#
# If this happens, it confirms that the real g cannot be found inside
# this same split torus-normaliser model.
############################################################

println("============================================================")
println("HYBRID ORDER-13 / ORDER-6 TORUS SANITY TEST")
println("============================================================")

############################################################
# Hybrid element:
#
#   (u, a, w)
#
# where:
#   u is an order-13 torus exponent vector mod 13
#   a is an order-6 torus exponent vector mod 6
#   w is a Weyl element
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
    return (Tuple([mod(ui,13) for ui in u]),
            Tuple([mod(ai,6) for ai in a]),
            MatKeyQ(w))
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

function Hybrid_Order(x; limit = 500)
    out = Hybrid_Identity()

    for k in 1:limit
        out = Hybrid_Mul(out, x)

        if Hybrid_IsIdentity(out)
            return k
        end
    end

    return 0
end

############################################################
# Trace on L(F4)
#
# Root contribution appears only from roots fixed by w.
# For fixed root alpha, eigenvalue is:
#
#   exp(2*pi*i*alpha(u)/13) * exp(2*pi*i*alpha(a)/6)
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
# Define the naive same-torus g, f, and the 9 t representatives
############################################################

g13_vec = [1, 1, 1, 1]       # from Kac tuple [1,1,1,1,2]
zero6 = [0,0,0,0]
zero13 = [0,0,0,0]

g_hybrid = (g13_vec, zero6, I4Q)
f_hybrid = (zero13, f_vec, I4Q)

println("Naive same-torus g vector mod 13 = ", g13_vec)
println("order(g) = ", Hybrid_Order(g_hybrid))
println("trace(g) = ", Hybrid_AdjointTrace(g_hybrid))
println("Expected trace(g) from order-13 F4 Kac class = 0")

println("order(f) = ", Hybrid_Order(f_hybrid))
println("trace(f) = ", Hybrid_AdjointTrace(f_hybrid))

############################################################
# Check action of f on this naive g
############################################################

fg = Hybrid_Mul(f_hybrid, g_hybrid)
gf = Hybrid_Mul(g_hybrid, f_hybrid)

println("Does this naive f commute with this naive g? ", Hybrid_Key(fg) == Hybrid_Key(gf))
println("So in this same-torus model, f acts on <g> by exponent 1, not exponent 10.")

############################################################
# Test Bruhat order-3 relation for the 9 t representatives
############################################################

println("------------------------------------------------------------")
println("Testing order(g^k * t) for the 9 t orbit representatives")
println("------------------------------------------------------------")

same_torus_bruhat_hits = []

for i in 1:length(orbit_data)
    sz, rep, orb = orbit_data[i]
    a_t, w_t = rep

    t_hybrid = (zero13, a_t, w_t)

    order_t = Hybrid_Order(t_hybrid)
    trace_t = Hybrid_AdjointTrace(t_hybrid)

    order3_k = []

    for k in 0:12
        elem = Hybrid_Mul(Hybrid_Pow(g_hybrid, k), t_hybrid)
        ord = Hybrid_Order(elem)

        if ord == 3
            push!(order3_k, k)
        end
    end

    push!(same_torus_bruhat_hits, (i, order3_k))

    println("Orbit ", i)
    println("  t vector a = ", a_t)
    println("  order(t) = ", order_t)
    println("  trace(t) = ", trace_t)
    println("  k with order(g^k*t)=3 = ", order3_k)
    println("------------------------------------------------------------")
end

############################################################
# Final conclusion
############################################################

println("Summary:")
for row in same_torus_bruhat_hits
    i, order3_k = row
    println("Orbit ", i, " has order-3 k-values: ", order3_k)
end

println("------------------------------------------------------------")
println("Conclusion")
println("------------------------------------------------------------")
println("The same-torus placement gives trace(g)=0, but it is too small.")
println("In this model, f centralises g, so it cannot realise 13:6.")
println("Also, no t representative gives the PSL2(13) Bruhat relation order(g^k*t)=3.")
println("Therefore the real order-13 element g must be introduced outside this same torus-normaliser model.")
println("This is exactly the point where a genuine F4(7) construction or a larger module model is needed.")

println("============================================================")
println("END FULL F4(7) WALTON-STYLE TORUS-NORMALISER SCRIPT")
println("============================================================")

############################################################
# Observed local f,t result from previous run:
#
# The 9 orbit representatives all satisfied:
#
#   order(t) = 2
#   trace(t) = -4
#   t*f*t^{-1} = f^{-1}
#   order(f*t) = 2
#   size <f,t> = 12
#
# Summary table from the previous run:
#
# orbit | orbit_size | a              | order(t) | trace(t) | inverts f | order(f*t) | size<f,t>
#   1   | 81         | [0, 1, 4, 1]   | 2        | -4       | true      | 2          | 12
#   2   | 81         | [0, 2, 2, 5]   | 2        | -4       | true      | 2          | 12
#   3   | 81         | [4, 1, 4, 0]   | 2        | -4       | true      | 2          | 12
#   4   | 81         | [4, 0, 2, 2]   | 2        | -4       | true      | 2          | 12
#   5   | 162        | [4, 5, 1, 3]   | 2        | -4       | true      | 2          | 12
#   6   | 162        | [1, 4, 0, 4]   | 2        | -4       | true      | 2          | 12
#   7   | 162        | [5, 3, 4, 5]   | 2        | -4       | true      | 2          | 12
#   8   | 162        | [0, 2, 1, 3]   | 2        | -4       | true      | 2          | 12
#   9   | 324        | [1, 2, 5, 3]   | 2        | -4       | true      | 2          | 12
#
############################################################
