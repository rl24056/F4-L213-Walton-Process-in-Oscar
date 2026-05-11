############################################################
# F4(7) WALTON-STYLE STRUCTURAL g-f-t SEARCH
#
# GitHub-ready single GAP/OSCAR script.
#
# Intended use:
#
#   julia
#   julia> using Oscar
#   julia> GAP.prompt()
#   gap> Read("f4_7_walton_structural_gft_search_steps_32_to_37.g");
#
# Main purpose:
#   1. Build the manual adjoint F4(7) matrix group on L(F4), dim 52.
#   2. Construct Weyl reflection lifts from root group matrices.
#   3. Freeze a deterministic order-6 structural element f32B.
#   4. Extract the root permutation/Weyl action of f32B.
#   5. Solve for order-13 Kac-residue lines compatible with g^f = g^10.
#   6. Build an extension-field torus element gExt32 over GF(7^12).
#   7. Verify BExt=<gExt32,fExt32> has the expected 13:6 order distribution.
#   8. Search Weyl-lift exact-inverting involutions t and test Bruhat/order-3 witnesses.
#
# Mathematical target:
#
#       |g| = 13,
#       |f| = 6,
#       g^f = g^10,
#       <g,f> ~= 13:6,
#       |t| = 2,
#       f^t = f^-1,
#       trace(t on L(F4)) = -4,
#       t notin <g,f>,
#       t does not normalise <g>,
#       and for some b in <g,f>, (b*t)^3 = 1.
#
# Notes:
#   - This avoids Normalizer(G32B,P32B) and RepresentativeAction.
#   - The old/random g-search and the old Step 34 diagnostic are included
#     but disabled by default, because the structural Kac/extension-field route
#     is the successful route.
#   - The old full Step 37A is also disabled by default because Step 37A FAST
#     is the practical version.
############################################################

Print("\n============================================================\n");
Print("F4(7) WALTON-STYLE STRUCTURAL g-f-t SEARCH\n");
Print("============================================================\n");

############################################################
# GLOBAL RUN FLAGS
############################################################

# This old random search is included for reference, but the successful route
# uses Kac-residue lines and GF(7^12), so the default is false.
RUN_RANDOM_FIXED_F_G_SEARCH_32 := false;;

# Old Step 34 assumes GAP's RootSystem labels simple roots as standard unit
# vectors. That assumption was later corrected by Step 34B.
RUN_OLD_STEP_34_DIAGNOSTIC_32 := false;;

# Original Step 37A tries Bruhat witnesses inside the full enumeration loop
# and can be slow. The practical route is Step 37A FAST, then 37B/C/D.
RUN_SLOW_STEP_37A_FULL_32 := false;;

############################################################
# STRUCTURAL f FIRST:
# Manual adjoint F4(7), then construct order-6 Weyl-lift
# candidates f from root reflection lifts.
#
# This avoids:
#   Normalizer(G32B, P32B)
#   RepresentativeAction(G32B, g32B, g32B^10, OnPoints)
#
# Goal:
#   Build actual matrix group G32B <= GL(52,7)
#   Construct Weyl-lift elements inside G32B
#   Find f32B with:
#
#       Order(f32B) = 6
#       Trace(f32B)   =  2
#       Trace(f32B^2) = -2
#       Trace(f32B^3) = -4
#
# Over GF(7), this means:
#
#       2, 5, 3
#
# This is the structural version of the old Kac/Weyl f.
############################################################

Print("\n============================================================\n");
Print("STRUCTURAL f FIRST: ADJOINT F4(7) WEYL-LIFT SEARCH\n");
Print("============================================================\n");

############################################################
# PARAMETERS
############################################################

F32 := GF(7);;

MAX_WEYL_RANDOM_TRIALS := 5000;;
MAX_WEYL_WORD_LENGTH := 20;;

trace_f_target := 2 * One(F32);;
trace_f2_target := -2 * One(F32);;
trace_f3_target := -4 * One(F32);;

Print("Field = GF(7)\n");
Print("MAX_WEYL_RANDOM_TRIALS = ", MAX_WEYL_RANDOM_TRIALS, "\n");
Print("MAX_WEYL_WORD_LENGTH = ", MAX_WEYL_WORD_LENGTH, "\n");

############################################################
# BASIC HELPERS
############################################################

Rand32 := function(G)
    if IsBoundGlobal("PseudoRandom") then
        return PseudoRandom(G);
    else
        return Random(G);
    fi;
end;;

Trace32 := function(x)
    return TraceMat(x);
end;;

GoodTraceProfileF32 := function(x)
    if Trace32(x) <> trace_f_target then
        return false;
    fi;

    if Trace32(x^2) <> trace_f2_target then
        return false;
    fi;

    if Trace32(x^3) <> trace_f3_target then
        return false;
    fi;

    return true;
end;;

RootGroupMatrix32 := function(A, t)
    local M, P, k, coef, denom;

    M := A^0;
    P := A^0;

    for k in [1..6] do
        P := P * A;

        if P = 0 * P then
            break;
        fi;

        denom := Factorial(k) * One(t);
        coef := (t^k) / denom;

        M := M + coef * P;
    od;

    return M;
end;;

############################################################
# PART 1. BUILD LIE ALGEBRA L(F4) OVER GF(7)
############################################################

Print("\n============================================================\n");
Print("PART 1: BUILD LIE ALGEBRA L(F4) OVER GF(7)\n");
Print("============================================================\n");

L32 := SimpleLieAlgebra("F", 4, F32);;

Print("Constructed L32 := SimpleLieAlgebra(\"F\",4,GF(7))\n");
Print("Dimension(L32) = ", Dimension(L32), "\n");

CB32 := ChevalleyBasis(L32);;

pos32 := CB32[1];;
neg32 := CB32[2];;
cart32 := CB32[3];;

Print("Length positive root vectors = ", Length(pos32), "\n");
Print("Length negative root vectors = ", Length(neg32), "\n");
Print("Length Cartan elements        = ", Length(cart32), "\n");

basisList32 := Concatenation(pos32, neg32, cart32);;
BAS32 := Basis(L32, basisList32);;

Print("Basis length = ", Length(basisList32), "\n");

if Length(basisList32) <> 52 then
    Error("Basis length is not 52.\n");
fi;

############################################################
# PART 2. BUILD ROOT GROUP MATRICES
############################################################

Print("\n============================================================\n");
Print("PART 2: BUILD ROOT GROUP MATRICES\n");
Print("============================================================\n");

rootPosMats32 := [];;
rootNegMats32 := [];;

for x in pos32 do
    A := AdjointMatrix(BAS32, x);
    Add(rootPosMats32, RootGroupMatrix32(A, One(F32)));
od;

for x in neg32 do
    A := AdjointMatrix(BAS32, x);
    Add(rootNegMats32, RootGroupMatrix32(A, One(F32)));
od;

rootMats32 := Concatenation(rootPosMats32, rootNegMats32);;

Print("Number of positive root group matrices = ", Length(rootPosMats32), "\n");
Print("Number of negative root group matrices = ", Length(rootNegMats32), "\n");
Print("Total root group generators = ", Length(rootMats32), "\n");
Print("Matrix dimension = ", Length(rootMats32[1]), "\n");

############################################################
# PART 3. BUILD ACTUAL ADJOINT MATRIX GROUP
############################################################

Print("\n============================================================\n");
Print("PART 3: BUILD ACTUAL ADJOINT MATRIX GROUP G32B\n");
Print("============================================================\n");

G32B := Group(rootMats32);;

Print("Constructed G32B := Group(root group matrices)\n");
Print("Number of generators of G32B = ", Length(GeneratorsOfGroup(G32B)), "\n");
Print("We do not compute Size(G32B).\n");

############################################################
# PART 4. CONSTRUCT WEYL REFLECTION LIFTS
#
# For each positive root alpha:
#
#   n_alpha(1) = x_alpha(1) x_{-alpha}(-1) x_alpha(1)
#
# This gives an actual matrix representative of the root
# reflection inside the adjoint group.
############################################################

Print("\n============================================================\n");
Print("PART 4: CONSTRUCT WEYL REFLECTION LIFTS\n");
Print("============================================================\n");

WeylLiftFromRootIndex32 := function(i)
    local Apos, Aneg, xpos, xnegminus, nalpha;

    Apos := AdjointMatrix(BAS32, pos32[i]);
    Aneg := AdjointMatrix(BAS32, neg32[i]);

    xpos := RootGroupMatrix32(Apos, One(F32));
    xnegminus := RootGroupMatrix32(Aneg, -One(F32));

    nalpha := xpos * xnegminus * xpos;

    return nalpha;
end;;

WeylLifts32 := [];;

for i in [1..Length(pos32)] do
    Add(WeylLifts32, WeylLiftFromRootIndex32(i));
od;

Print("Number of Weyl reflection lifts constructed = ",
      Length(WeylLifts32), "\n");

Print("Checking orders of the first few Weyl lifts:\n");

for i in [1..Minimum(Length(WeylLifts32), 10)] do
    Print("  lift ", i, " has order ", Order(WeylLifts32[i]), "\n");
od;

############################################################
# PART 5. RANDOM SEARCH INSIDE THE WEYL-LIFT GROUP
#
# We search for an actual matrix f with:
#
#   Order(f)=6
#   Trace(f)=2
#   Trace(f^2)=-2
#   Trace(f^3)=-4
#
# This should be much lighter than the previous global
# normalizer/conjugator computations.
############################################################

Print("\n============================================================\n");
Print("PART 5: SEARCH FOR STRUCTURAL WEYL-LIFT f\n");
Print("============================================================\n");

f32B := fail;;
f32B_word := fail;;

Identity32 := rootMats32[1]^0;;

for trial in [1..MAX_WEYL_RANDOM_TRIALS] do

    wordLength := Random([1..MAX_WEYL_WORD_LENGTH]);
    x := Identity32;
    word := [];;

    for j in [1..wordLength] do
        idx := Random([1..Length(WeylLifts32)]);
        x := x * WeylLifts32[idx];
        Add(word, idx);
    od;

    if Order(x) = 6 then

        if GoodTraceProfileF32(x) then
            f32B := x;;
            f32B_word := word;;
            Print("Found structural f32B at trial ", trial, "\n");
            break;
        fi;

    fi;

    if trial mod 500 = 0 then
        Print("Weyl random trials completed: ", trial, "\n");
    fi;

od;

############################################################
# PART 6. IF RANDOM FAILS, TRY ENUMERATING THE WEYL-LIFT GROUP
############################################################

if f32B = fail then

    Print("\nRandom Weyl-lift search did not find f.\n");
    Print("Now trying to build Wlift32 := Group(WeylLifts32).\n");
    Print("This should be much smaller than G32B.\n");

    Wlift32 := Group(WeylLifts32);;

    Print("Constructed Wlift32.\n");
    Print("Number of generators of Wlift32 = ",
          Length(GeneratorsOfGroup(Wlift32)), "\n");

    sizeW32 := Size(Wlift32);;

    Print("Size(Wlift32) = ", sizeW32, "\n");

    if sizeW32 <= 100000 then

        Print("Enumerating Wlift32 elements.\n");

        for x in Elements(Wlift32) do

            if Order(x) = 6 and GoodTraceProfileF32(x) then
                f32B := x;;
                f32B_word := "found by enumeration";;
                break;
            fi;

        od;

    else
        Print("Wlift32 unexpectedly large; skipping enumeration.\n");
    fi;

fi;

############################################################
# PART 7. REPORT
############################################################

Print("\n============================================================\n");
Print("PART 7: REPORT STRUCTURAL f\n");
Print("============================================================\n");

if f32B = fail then

    Print("No structural f32B found in this random/enumeration run.\n");
    Print("This is okay because the next audit block freezes the known deterministic word.\n");

else

    Print("FOUND STRUCTURAL f32B.\n");
    Print("Order(f32B) = ", Order(f32B), "\n");
    Print("Trace(f32B)   = ", Trace32(f32B), "\n");
    Print("Trace(f32B^2) = ", Trace32(f32B^2), "\n");
    Print("Trace(f32B^3) = ", Trace32(f32B^3), "\n");
    Print("Good trace profile? ", GoodTraceProfileF32(f32B), "\n");

    Print("\nf32B_word = ");
    Print(f32B_word, "\n");

fi;

Print("\nStored objects:\n");
Print("  G32B\n");
Print("  L32\n");
Print("  BAS32\n");
Print("  rootMats32\n");
Print("  WeylLifts32\n");

Print("\nInterpretation:\n");
Print("The deterministic audit block below freezes the known structural f32B.\n");
Print("The next serious step is to construct an order-13 g in an f32B-stable torus with g^f = g^10.\n");

Print("\n============================================================\n");
Print("STRUCTURAL f FIRST BLOCK FINISHED\n");
Print("============================================================\n");

############################################################
# AUDIT AND FREEZE STRUCTURAL f32B
############################################################

Print("\n============================================================\n");
Print("AUDIT: FREEZE STRUCTURAL f32B\n");
Print("============================================================\n");

f32B_word_fixed := [5,24,2,14,8,17,9,6,7,16,5,23,19,9,3,6,6,15,9,1];;

f32B_fixed := Identity32;;

for idx in f32B_word_fixed do
    f32B_fixed := f32B_fixed * WeylLifts32[idx];
od;

Print("Order(f32B_fixed) = ", Order(f32B_fixed), "\n");
Print("Trace(f32B_fixed)   = ", Trace32(f32B_fixed), "\n");
Print("Trace(f32B_fixed^2) = ", Trace32(f32B_fixed^2), "\n");
Print("Trace(f32B_fixed^3) = ", Trace32(f32B_fixed^3), "\n");
Print("Good trace profile? ", GoodTraceProfileF32(f32B_fixed), "\n");

Print("Does f32B_fixed equal current f32B? ", f32B_fixed = f32B, "\n");

f32B := f32B_fixed;;

Print("\nFrozen f32B successfully.\n");
Print("From now on use this deterministic f32B, not a new random one.\n");

Print("\n============================================================\n");
Print("AUDIT FINISHED\n");
Print("============================================================\n");

############################################################
# OPTIONAL OLD NEXT STEP:
# Find order-13 g normalised by the fixed structural f32B
#
# We already have:
#   G32B
#   f32B
#
# Target:
#   Order(g32B)=13
#   Trace(g32B)=0
#   g32B^f32B = g32B^10
#
# This is a bounded targeted search.
# It does NOT use:
#   Normalizer(G32B,<g>)
#   RepresentativeAction(...)
#
# This block is disabled by default because the successful route is
# Step 34B/35/36, which constructs g structurally from Kac residues.
############################################################

if RUN_RANDOM_FIXED_F_G_SEARCH_32 then

Print("\n============================================================\n");
Print("OPTIONAL SEARCH FOR g NORMALISED BY FIXED STRUCTURAL f32B\n");
Print("============================================================\n");

MAX_G_WITH_FIXED_F_TRIALS := 10000;;

trace_g_target := Zero(F32);;

ActionExponentGUnderF32 := function(g, f)
    local image, k;

    image := g^f;

    for k in [1..12] do
        if image = g^k then
            return k;
        fi;
    od;

    return fail;
end;;

GoodTraceProfileF32 := function(x)
    if Trace32(x) <> trace_f_target then
        return false;
    fi;

    if Trace32(x^2) <> trace_f2_target then
        return false;
    fi;

    if Trace32(x^3) <> trace_f3_target then
        return false;
    fi;

    return true;
end;;

Print("Checking fixed f32B first:\n");
Print("Order(f32B) = ", Order(f32B), "\n");
Print("Trace(f32B)   = ", Trace32(f32B), "\n");
Print("Trace(f32B^2) = ", Trace32(f32B^2), "\n");
Print("Trace(f32B^3) = ", Trace32(f32B^3), "\n");
Print("Good trace profile for f32B? ", GoodTraceProfileF32(f32B), "\n");

Print("\nAlso checking f32B^-1:\n");
Print("Order(f32B^-1) = ", Order(f32B^-1), "\n");
Print("Trace(f32B^-1)   = ", Trace32(f32B^-1), "\n");
Print("Trace((f32B^-1)^2) = ", Trace32((f32B^-1)^2), "\n");
Print("Trace((f32B^-1)^3) = ", Trace32((f32B^-1)^3), "\n");
Print("Good trace profile for f32B^-1? ", GoodTraceProfileF32(f32B^-1), "\n");

g32B := fail;;
f_for_B32B := fail;;
g_trial_found := 0;;
g_action_exp := fail;;

for trial in [1..MAX_G_WITH_FIXED_F_TRIALS] do

    x := Rand32(G32B);
    ox := Order(x);

    if ox mod 13 = 0 then

        cand := x^(ox / 13);

        if Order(cand) = 13 then

            if Trace32(cand) = trace_g_target then

                exp := ActionExponentGUnderF32(cand, f32B);

                if exp = 10 then
                    g32B := cand;;
                    f_for_B32B := f32B;;
                    g_trial_found := trial;;
                    g_action_exp := exp;;
                    Print("Found g32B with exponent 10 at trial ", trial, "\n");
                    break;
                fi;

                # If f acts by 4, then f^-1 acts by 10.
                # This is the same 13:6 orientation, just with f inverted.
                if exp = 4 then
                    if GoodTraceProfileF32(f32B^-1) then
                        g32B := cand;;
                        f_for_B32B := f32B^-1;;
                        g_trial_found := trial;;
                        g_action_exp := ActionExponentGUnderF32(cand, f_for_B32B);;
                        Print("Found g32B with exponent 4 for f32B at trial ", trial, "\n");
                        Print("Using f_for_B32B := f32B^-1, which acts by exponent ",
                              g_action_exp, "\n");
                        break;
                    fi;
                fi;

            fi;

        fi;

    fi;

    if trial mod 500 = 0 then
        Print("Trials completed: ", trial, "\n");
    fi;

od;

Print("\n============================================================\n");
Print("REPORT: g SEARCH WITH FIXED f\n");
Print("============================================================\n");

if g32B = fail then

    Print("No suitable g32B found in ", MAX_G_WITH_FIXED_F_TRIALS, " trials.\n");
    Print("This does not disprove the construction.\n");
    Print("It means random extraction did not hit the f-stable order-13 torus.\n");
    Print("Next route is the structural torus construction using the Weyl/Kac vector.\n");

else

    P32B := Group(g32B);;
    B32B := Group(g32B, f_for_B32B);;

    Print("FOUND CANDIDATE MATRIX g32B.\n");
    Print("Found at trial ", g_trial_found, "\n");
    Print("Order(g32B) = ", Order(g32B), "\n");
    Print("Trace(g32B) = ", Trace32(g32B), "\n");
    Print("Order(P32B=<g32B>) = ", Order(P32B), "\n");

    Print("\nChosen f_for_B32B:\n");
    Print("Order(f_for_B32B) = ", Order(f_for_B32B), "\n");
    Print("Trace(f_for_B32B)   = ", Trace32(f_for_B32B), "\n");
    Print("Trace(f_for_B32B^2) = ", Trace32(f_for_B32B^2), "\n");
    Print("Trace(f_for_B32B^3) = ", Trace32(f_for_B32B^3), "\n");
    Print("Good trace profile? ", GoodTraceProfileF32(f_for_B32B), "\n");

    Print("\nAction check:\n");
    Print("g32B^f_for_B32B = g32B^",
          ActionExponentGUnderF32(g32B, f_for_B32B), "\n");

    Print("\nLocal subgroup:\n");
    Print("Order(B32B=<g32B,f_for_B32B>) = ", Order(B32B), "\n");

    if Order(B32B) = 78 then
        Print("\nSUCCESS:\n");
        Print("B32B=<g32B,f_for_B32B> is the actual matrix-level 13:6 subgroup.\n");
    else
        Print("\nWARNING:\n");
        Print("The action looked correct, but B32B does not have order 78.\n");
        Print("Check this candidate carefully.\n");
    fi;

fi;

Print("\n============================================================\n");
Print("OPTIONAL FIXED-f g SEARCH FINISHED\n");
Print("============================================================\n");

fi;

############################################################
# OPTIONAL OLD STEP 34:
# Extract the Weyl/root action of the fixed structural f32B
#
# This older version assumes GAP simple-root coordinates are
# [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1].
# That assumption was corrected later.
############################################################

if RUN_OLD_STEP_34_DIAGNOSTIC_32 then

Print("\n============================================================\n");
Print("OLD STEP 34: EXTRACT WEYL ACTION OF FIXED f32B\n");
Print("============================================================\n");

if not IsBound(f32B) then
    Error("f32B is not bound. Run the structural f block first.\n");
fi;

if not IsBound(BAS32) then
    Error("BAS32 is not bound. Run the Lie algebra construction first.\n");
fi;

if not IsBound(pos32) then
    Error("pos32 is not bound.\n");
fi;

if not IsBound(neg32) then
    Error("neg32 is not bound.\n");
fi;

Print("Order(f32B) = ", Order(f32B), "\n");
Print("Trace(f32B)   = ", Trace32(f32B), "\n");
Print("Trace(f32B^2) = ", Trace32(f32B^2), "\n");
Print("Trace(f32B^3) = ", Trace32(f32B^3), "\n");

RootImageIndexAndScalar32 := function(M, i)
    local row, nz, j;

    row := M[i];
    nz := [];

    for j in [1..48] do
        if row[j] <> Zero(F32) then
            Add(nz, j);
        fi;
    od;

    if Length(nz) <> 1 then
        return fail;
    fi;

    return [nz[1], row[nz[1]]];
end;;

rootPerm32 := [];;
rootScalars32 := [];;
badRootImages32 := [];;

for i in [1..48] do
    img := RootImageIndexAndScalar32(f32B, i);

    if img = fail then
        Add(badRootImages32, i);
    else
        rootPerm32[i] := img[1];
        rootScalars32[i] := img[2];
    fi;
od;

Print("\nNumber of bad root images = ", Length(badRootImages32), "\n");

if Length(badRootImages32) > 0 then
    Print("Bad root image indices: ", badRootImages32, "\n");
    Error("f32B is not monomial on root spaces in the expected basis.\n");
fi;

Print("Success: f32B permutes the 48 root spaces up to scalars.\n");

RootPermCycleLengths32 := function(perm)
    local seen, cycles, i, cur, len;

    seen := List([1..48], x -> false);
    cycles := [];

    for i in [1..48] do
        if not seen[i] then
            cur := i;
            len := 0;

            while not seen[cur] do
                seen[cur] := true;
                len := len + 1;
                cur := perm[cur];
            od;

            Add(cycles, len);
        fi;
    od;

    return cycles;
end;;

cycleLengths32 := RootPermCycleLengths32(rootPerm32);;

Print("Root-space permutation cycle lengths:\n");
Print(cycleLengths32, "\n");

Print("\nTrying to access RootSystem(L32) and PositiveRoots.\n");

if not IsBoundGlobal("RootSystem") then
    Error("RootSystem function is not available in this GAP session.\n");
fi;

R32 := RootSystem(L32);;

Print("RootSystem(L32) constructed.\n");

posRoots32 := PositiveRoots(R32);;
negRoots32 := NegativeRoots(R32);;

Print("Number of positive roots from RootSystem = ", Length(posRoots32), "\n");
Print("Number of negative roots from RootSystem = ", Length(negRoots32), "\n");

if Length(posRoots32) <> 24 then
    Error("PositiveRoots(R32) does not have length 24.\n");
fi;

if Length(negRoots32) <> 24 then
    Error("NegativeRoots(R32) does not have length 24.\n");
fi;

allRoots32 := Concatenation(posRoots32, negRoots32);;

Print("First few positive roots from GAP RootSystem:\n");
for i in [1..Minimum(5, Length(posRoots32))] do
    Print("  posRoots32[", i, "] = ", posRoots32[i], "\n");
od;

RootAsList32 := function(r)
    return List(r, x -> Int(x));
end;;

allRootsList32 := List(allRoots32, RootAsList32);;

simpleRootCoords32 := [
    [1,0,0,0],
    [0,1,0,0],
    [0,0,1,0],
    [0,0,0,1]
];;

simpleRootIndices32 := [];;

for s in simpleRootCoords32 do
    pos := Position(allRootsList32, s);

    if pos = fail then
        Error("Could not find simple root ", s, " in allRootsList32.\n");
    fi;

    Add(simpleRootIndices32, pos);
od;

Print("\nSimple root indices in allRoots32:\n");
Print(simpleRootIndices32, "\n");

Wrows32 := [];;

for i in [1..4] do
    idx := simpleRootIndices32[i];
    imageIdx := rootPerm32[idx];
    Add(Wrows32, allRootsList32[imageIdx]);
od;

Print("\nRows of Weyl action matrix W from simple-root images:\n");
for row in Wrows32 do
    Print(row, "\n");
od;

Mod13 := function(a)
    return ((a mod 13) + 13) mod 13;
end;;

VecMatMod13 := function(v, M)
    local res, j, i, s;

    res := [];

    for j in [1..Length(M[1])] do
        s := 0;

        for i in [1..Length(v)] do
            s := s + v[i] * M[i][j];
        od;

        Add(res, Mod13(s));
    od;

    return res;
end;;

ScalarVecMod13 := function(c, v)
    return List(v, x -> Mod13(c*x));
end;;

IsZeroVecMod13 := function(v)
    return ForAll(v, x -> Mod13(x) = 0);
end;;

SameProjectiveLineMod13 := function(v, w)
    local c;

    for c in [1..12] do
        if ScalarVecMod13(c, v) = List(w, Mod13) then
            return true;
        fi;
    od;

    return false;
end;;

NormalizeProjectiveMod13 := function(v)
    local i, inv, c;

    v := List(v, Mod13);

    for i in [1..Length(v)] do
        if v[i] <> 0 then
            for c in [1..12] do
                if Mod13(c * v[i]) = 1 then
                    inv := c;
                    return ScalarVecMod13(inv, v);
                fi;
            od;
        fi;
    od;

    return v;
end;;

Print("\nSolving v * W = 10 v mod 13.\n");

Eigen10Lines32 := [];;

for a in [0..12] do
for b in [0..12] do
for c in [0..12] do
for d in [0..12] do

    v := [a,b,c,d];

    if not IsZeroVecMod13(v) then
        lhs := VecMatMod13(v, Wrows32);
        rhs := ScalarVecMod13(10, v);

        if lhs = rhs then
            rep := NormalizeProjectiveMod13(v);

            if not ForAny(Eigen10Lines32, u -> u = rep) then
                Add(Eigen10Lines32, rep);
            fi;
        fi;
    fi;

od;
od;
od;
od;

Print("Number of projective eigenlines for eigenvalue 10 = ",
      Length(Eigen10Lines32), "\n");

for i in [1..Length(Eigen10Lines32)] do
    Print("  eigenline ", i, ": ", Eigen10Lines32[i], "\n");
od;

Print("\nSolving v * W = 4 v mod 13.\n");

Eigen4Lines32 := [];;

for a in [0..12] do
for b in [0..12] do
for c in [0..12] do
for d in [0..12] do

    v := [a,b,c,d];

    if not IsZeroVecMod13(v) then
        lhs := VecMatMod13(v, Wrows32);
        rhs := ScalarVecMod13(4, v);

        if lhs = rhs then
            rep := NormalizeProjectiveMod13(v);

            if not ForAny(Eigen4Lines32, u -> u = rep) then
                Add(Eigen4Lines32, rep);
            fi;
        fi;
    fi;

od;
od;
od;
od;

Print("Number of projective eigenlines for eigenvalue 4 = ",
      Length(Eigen4Lines32), "\n");

for i in [1..Length(Eigen4Lines32)] do
    Print("  eigenline ", i, ": ", Eigen4Lines32[i], "\n");
od;

Print("\n============================================================\n");
Print("OLD STEP 34 FINISHED\n");
Print("============================================================\n");

fi;

############################################################
# STEP 34B:
# Corrected Weyl-action extraction for fixed f32B
#
# Fixes the previous error:
#   GAP's RootSystem(L32) does NOT label simple roots as
#   [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1].
#
# Instead:
#   choose four independent roots automatically,
#   compute the Weyl action of f32B on that basis,
#   then print the induced 4x4 matrix.
############################################################

Print("\n============================================================\n");
Print("STEP 34B: CORRECTED WEYL ACTION OF f32B\n");
Print("============================================================\n");

############################################################
# PART 0. Recheck f32B
############################################################

Print("Order(f32B) = ", Order(f32B), "\n");
Print("Trace(f32B)   = ", Trace32(f32B), "\n");
Print("Trace(f32B^2) = ", Trace32(f32B^2), "\n");
Print("Trace(f32B^3) = ", Trace32(f32B^3), "\n");

############################################################
# PART 1. Recompute root-space permutation
############################################################

RootImageIndexAndScalar32 := function(M, i)
    local row, nz, j;

    row := M[i];
    nz := [];

    for j in [1..48] do
        if row[j] <> Zero(F32) then
            Add(nz, j);
        fi;
    od;

    if Length(nz) <> 1 then
        return fail;
    fi;

    return [nz[1], row[nz[1]]];
end;;

rootPerm32 := [];;
rootScalars32 := [];;
badRootImages32 := [];;

for i in [1..48] do
    img := RootImageIndexAndScalar32(f32B, i);

    if img = fail then
        Add(badRootImages32, i);
    else
        rootPerm32[i] := img[1];
        rootScalars32[i] := img[2];
    fi;
od;

Print("\nNumber of bad root images = ", Length(badRootImages32), "\n");

if Length(badRootImages32) > 0 then
    Print("Bad root image indices: ", badRootImages32, "\n");
    Error("f32B is not monomial on root spaces.\n");
fi;

Print("Success: f32B permutes the 48 root spaces up to scalars.\n");

############################################################
# PART 2. Cycle lengths of root permutation
############################################################

RootPermCycleLengths32 := function(perm)
    local seen, cycles, i, cur, len;

    seen := List([1..48], x -> false);
    cycles := [];

    for i in [1..48] do
        if not seen[i] then
            cur := i;
            len := 0;

            while not seen[cur] do
                seen[cur] := true;
                len := len + 1;
                cur := perm[cur];
            od;

            Add(cycles, len);
        fi;
    od;

    return cycles;
end;;

cycleLengths32 := RootPermCycleLengths32(rootPerm32);;

Print("Root-space permutation cycle lengths:\n");
Print(cycleLengths32, "\n");

############################################################
# PART 3. Get GAP root-system coordinates
############################################################

R32 := RootSystem(L32);;

posRoots32 := PositiveRoots(R32);;
negRoots32 := NegativeRoots(R32);;

allRoots32 := Concatenation(posRoots32, negRoots32);;

Print("\nNumber of positive roots = ", Length(posRoots32), "\n");
Print("Number of negative roots = ", Length(negRoots32), "\n");

if Length(allRoots32) <> 48 then
    Error("Expected 48 total roots.\n");
fi;

############################################################
# PART 4. Choose four independent roots automatically
############################################################

basisRootIndices32 := [];;
basisRootsGF32 := [];;

for i in [1..48] do

    candidateBasis := Concatenation(basisRootsGF32, [allRoots32[i]]);

    if RankMat(candidateBasis) > Length(basisRootsGF32) then
        Add(basisRootsGF32, allRoots32[i]);
        Add(basisRootIndices32, i);
    fi;

    if Length(basisRootsGF32) = 4 then
        break;
    fi;

od;

Print("\nChosen independent root indices:\n");
Print(basisRootIndices32, "\n");

Print("Chosen independent root vectors over GF(7):\n");
for i in [1..4] do
    Print("  basis root ", i, " index ", basisRootIndices32[i],
          " = ", basisRootsGF32[i], "\n");
od;

if Length(basisRootsGF32) <> 4 then
    Error("Could not find four independent roots.\n");
fi;

############################################################
# PART 5. Compute Weyl action matrix in this root basis
#
# If basis row vectors are b_i, and f sends b_i to image_i,
# we solve:
#
#   image_i = c_1 b_1 + ... + c_4 b_4.
#
# The coefficients c_i form row i of the Weyl action matrix.
############################################################

WbasisGF32 := [];;

for i in [1..4] do

    rootIndex := basisRootIndices32[i];
    imageIndex := rootPerm32[rootIndex];
    target := allRoots32[imageIndex];

    coeffs := SolutionMat(basisRootsGF32, target);

    if coeffs = fail then
        Error("Could not express image root in chosen basis.\n");
    fi;

    # Verify the solution.
    check := 0 * target;

    for j in [1..4] do
        check := check + coeffs[j] * basisRootsGF32[j];
    od;

    if check <> target then
        Error("Linear combination check failed.\n");
    fi;

    Add(WbasisGF32, coeffs);

od;

Print("\nWeyl action matrix over GF(7), in chosen root basis:\n");
for row in WbasisGF32 do
    Print(row, "\n");
od;

############################################################
# PART 6. Convert GF(7) entries to small signed integers
#
# This is only a diagnostic integer lift.
# It should NOT yet be treated as the final Kac-coordinate matrix.
############################################################

GF7ToSignedInt32 := function(a)
    local n;

    n := IntFFE(a);

    if n > 3 then
        return n - 7;
    else
        return n;
    fi;
end;;

WbasisInt32 := List(WbasisGF32,
                    row -> List(row, GF7ToSignedInt32));;

Print("\nSigned integer lift of WbasisGF32:\n");
for row in WbasisInt32 do
    Print(row, "\n");
od;

############################################################
# PART 7. Check order of this Weyl matrix action
############################################################

MatMulMod7Int32 := function(A, B)
    local C, i, j, k, s;

    C := [];

    for i in [1..4] do
        C[i] := [];

        for j in [1..4] do
            s := 0;

            for k in [1..4] do
                s := s + A[i][k] * B[k][j];
            od;

            C[i][j] := ((s mod 7) + 7) mod 7;
        od;
    od;

    return C;
end;;

Id4Int32 := [
    [1,0,0,0],
    [0,1,0,0],
    [0,0,1,0],
    [0,0,0,1]
];;

Wmod7Int32 := List(WbasisGF32,
                   row -> List(row, x -> IntFFE(x)));;

powerW32 := Id4Int32;;

for k in [1..12] do
    powerW32 := MatMulMod7Int32(powerW32, Wmod7Int32);

    if powerW32 = Id4Int32 then
        Print("\nOrder of W action modulo 7 appears to be ", k, "\n");
        break;
    fi;
od;

Print("\n============================================================\n");
Print("STEP 34B FINISHED\n");
Print("============================================================\n");

############################################################
# STEP 35:
# Solve directly for Kac-residue vectors v mod 13
# using the actual root permutation of fixed f32B.
#
# We use:
#   allRoots32
#   rootPerm32
#
# Condition for g^f = g^10:
#
#   k(w(alpha)) = 10*k(alpha) mod 13
#
# where:
#   k(alpha) = v dot alpha mod 13.
#
# This avoids assuming GAP's simple-root coordinates.
############################################################

Print("\n============================================================\n");
Print("STEP 35: SOLVE KAC-RESIDUE LINES FROM ROOT PERMUTATION\n");
Print("============================================================\n");

############################################################
# PART 0. Safety checks
############################################################

if not IsBound(allRoots32) then
    Error("allRoots32 is not bound. Run Step 34B first.\n");
fi;

if not IsBound(rootPerm32) then
    Error("rootPerm32 is not bound. Run Step 34B first.\n");
fi;

if Length(allRoots32) <> 48 then
    Error("allRoots32 should have length 48.\n");
fi;

if Length(rootPerm32) <> 48 then
    Error("rootPerm32 should have length 48.\n");
fi;

Print("Root data available: 48 roots and root permutation.\n");

############################################################
# PART 1. Convert GF(7) root coordinates to signed integers
############################################################

GF7ToSignedInt32 := function(a)
    local n;

    n := IntFFE(a);

    if n > 3 then
        return n - 7;
    else
        return n;
    fi;
end;;

RootSignedList32 := List(allRoots32,
                         r -> List(r, GF7ToSignedInt32));;

Print("\nFirst few signed root coordinates:\n");
for i in [1..Minimum(8, Length(RootSignedList32))] do
    Print("  root ", i, " = ", RootSignedList32[i],
          " maps to root ", rootPerm32[i],
          " = ", RootSignedList32[rootPerm32[i]], "\n");
od;

############################################################
# PART 2. Mod 13 helpers
############################################################

Mod13Z32 := function(n)
    return ((n mod 13) + 13) mod 13;
end;;

DotRootMod13_32 := function(v, r)
    local s, i;

    s := 0;

    for i in [1..4] do
        s := s + v[i] * r[i];
    od;

    return Mod13Z32(s);
end;;

ScalarVecMod13_32 := function(c, v)
    return List(v, x -> Mod13Z32(c*x));
end;;

NormalizeLineMod13_32 := function(v)
    local i, c;

    v := List(v, Mod13Z32);

    for i in [1..Length(v)] do
        if v[i] <> 0 then
            for c in [1..12] do
                if Mod13Z32(c*v[i]) = 1 then
                    return ScalarVecMod13_32(c, v);
                fi;
            od;
        fi;
    od;

    return v;
end;;

IsZeroVecMod13_32 := function(v)
    return ForAll(v, x -> Mod13Z32(x) = 0);
end;;

############################################################
# PART 3. Test whether v satisfies exponent condition
############################################################

LineSatisfiesExponent32 := function(v, exp)
    local i, a, b;

    for i in [1..48] do
        a := DotRootMod13_32(v, RootSignedList32[i]);
        b := DotRootMod13_32(v, RootSignedList32[rootPerm32[i]]);

        if b <> Mod13Z32(exp*a) then
            return false;
        fi;
    od;

    return true;
end;;

ResidueCountsForLine32 := function(v)
    local counts, r, a;

    counts := List([1..13], i -> 0);

    for r in RootSignedList32 do
        a := DotRootMod13_32(v, r);
        counts[a+1] := counts[a+1] + 1;
    od;

    return counts;
end;;

############################################################
# PART 4. Enumerate projective lines v in F_13^4
############################################################

FindKacLinesForExponent32 := function(exp)
    local lines, a, b, c, d, v, rep;

    lines := [];

    for a in [0..12] do
    for b in [0..12] do
    for c in [0..12] do
    for d in [0..12] do

        v := [a,b,c,d];

        if not IsZeroVecMod13_32(v) then

            if LineSatisfiesExponent32(v, exp) then
                rep := NormalizeLineMod13_32(v);

                if not ForAny(lines, u -> u = rep) then
                    Add(lines, rep);
                fi;
            fi;

        fi;

    od;
    od;
    od;
    od;

    return lines;
end;;

############################################################
# PART 5. Solve for exponent 10 and exponent 4
############################################################

KacLines10_32 := FindKacLinesForExponent32(10);;
KacLines4_32 := FindKacLinesForExponent32(4);;

Print("\nNumber of projective Kac-residue lines for exponent 10 = ",
      Length(KacLines10_32), "\n");

for i in [1..Length(KacLines10_32)] do
    counts := ResidueCountsForLine32(KacLines10_32[i]);

    Print("\nExponent-10 line ", i, ": ", KacLines10_32[i], "\n");
    Print("  residue counts 0..12 = ", counts, "\n");
    Print("  zero-root count = ", counts[1], "\n");
od;

Print("\nNumber of projective Kac-residue lines for exponent 4 = ",
      Length(KacLines4_32), "\n");

for i in [1..Length(KacLines4_32)] do
    counts := ResidueCountsForLine32(KacLines4_32[i]);

    Print("\nExponent-4 line ", i, ": ", KacLines4_32[i], "\n");
    Print("  residue counts 0..12 = ", counts, "\n");
    Print("  zero-root count = ", counts[1], "\n");
od;

############################################################
# PART 6. Highlight regular lines
#
# A regular order-13 element should have no root with residue 0.
# So zero-root count should be 0.
############################################################

Print("\nRegular exponent-10 candidates, zero-root count 0:\n");

for i in [1..Length(KacLines10_32)] do
    counts := ResidueCountsForLine32(KacLines10_32[i]);

    if counts[1] = 0 then
        Print("  line ", i, " = ", KacLines10_32[i], "\n");
    fi;
od;

Print("\nRegular exponent-4 candidates, zero-root count 0:\n");

for i in [1..Length(KacLines4_32)] do
    counts := ResidueCountsForLine32(KacLines4_32[i]);

    if counts[1] = 0 then
        Print("  line ", i, " = ", KacLines4_32[i], "\n");
    fi;
od;

Print("\n============================================================\n");
Print("STEP 35 FINISHED\n");
Print("============================================================\n");

############################################################
# STEP 36:
# Build extension-field torus element gExt from Kac line
#
# We now know regular Kac-residue lines v mod 13.
#
# Since GF(7) does not contain primitive 13th roots of unity,
# we first build the torus element over GF(7^12).
#
# Goal:
#   For a regular exponent-10 line v, build gExt such that:
#
#       Order(gExt)=13
#       Trace(gExt)=0
#       gExt^fExt = gExt^10
#
# This confirms the structural torus construction.
############################################################

Print("\n============================================================\n");
Print("STEP 36: BUILD EXTENSION-FIELD TORUS ELEMENT gExt\n");
Print("============================================================\n");

############################################################
# PART 0. Safety checks
############################################################

if not IsBound(f32B) then
    Error("f32B is not bound.\n");
fi;

if not IsBound(RootSignedList32) then
    Error("RootSignedList32 is not bound. Run Step 35 first.\n");
fi;

if not IsBound(KacLines10_32) then
    Error("KacLines10_32 is not bound. Run Step 35 first.\n");
fi;

if not IsBound(KacLines4_32) then
    Error("KacLines4_32 is not bound. Run Step 35 first.\n");
fi;

Print("Order(f32B) = ", Order(f32B), "\n");
Print("Trace(f32B)   = ", Trace32(f32B), "\n");
Print("Trace(f32B^2) = ", Trace32(f32B^2), "\n");
Print("Trace(f32B^3) = ", Trace32(f32B^3), "\n");

############################################################
# PART 1. Extension field GF(7^12)
#
# Since 7 has order 12 modulo 13, primitive 13th roots
# of unity lie in GF(7^12).
############################################################

K13_32 := GF(7^12);;

zeta13_32 := Z(7^12)^((7^12 - 1)/13);;

Print("\nConstructed K13_32 := GF(7^12)\n");
Print("Order(zeta13_32) = ", Order(zeta13_32), "\n");

if Order(zeta13_32) <> 13 then
    Error("zeta13_32 does not have order 13.\n");
fi;

############################################################
# PART 2. Matrix conversion GF(7) -> GF(7^12)
############################################################

LiftMatrixToK13_32 := function(M)
    local rows, i, j, row;

    rows := [];

    for i in [1..Length(M)] do
        row := [];

        for j in [1..Length(M[i])] do
            Add(row, M[i][j] * One(K13_32));
        od;

        Add(rows, row);
    od;

    return rows;
end;;

fExt32 := LiftMatrixToK13_32(f32B);;

Print("Lifted f32B to fExt32 over GF(7^12).\n");
Print("Order(fExt32) = ", Order(fExt32), "\n");

############################################################
# PART 3. Build diagonal matrix from Kac line
#
# On a root vector e_alpha:
#
#       gExt acts by zeta13_32^{k(alpha)}
#
# where:
#
#       k(alpha) = v dot alpha mod 13.
#
# On the 4-dimensional Cartan part, gExt acts trivially.
############################################################

DiagonalMatrixFromEntriesK13_32 := function(entries)
    local n, M, i;

    n := Length(entries);
    M := NullMat(n, n, K13_32);

    for i in [1..n] do
        M[i][i] := entries[i];
    od;

    return M;
end;;

BuildGExtFromKacLine32 := function(v)
    local entries, i, res;

    entries := [];

    # 48 root-space entries
    for i in [1..48] do
        res := DotRootMod13_32(v, RootSignedList32[i]);
        Add(entries, zeta13_32^res);
    od;

    # 4 Cartan entries
    for i in [1..4] do
        Add(entries, One(K13_32));
    od;

    return DiagonalMatrixFromEntriesK13_32(entries);
end;;

############################################################
# PART 4. Test regular exponent-10 lines
############################################################

Print("\nTesting regular exponent-10 Kac lines.\n");

GoodGExt10Lines32 := [];;

Id52K13_32 := IdentityMat(52, K13_32);;

for i in [1..Length(KacLines10_32)] do

    counts := ResidueCountsForLine32(KacLines10_32[i]);

    if counts[1] = 0 then

        gExt := BuildGExtFromKacLine32(KacLines10_32[i]);

        Print("\nExponent-10 regular line ", i, ": ",
              KacLines10_32[i], "\n");

        Print("  gExt^13 = identity? ", gExt^13 = Id52K13_32, "\n");
        Print("  gExt = identity? ", gExt = Id52K13_32, "\n");
        Print("  Trace(gExt) = ", TraceMat(gExt), "\n");

        rel10 := (gExt^fExt32 = gExt^10);
        rel4  := (gExt^fExt32 = gExt^4);

        Print("  Relation gExt^fExt32 = gExt^10 ? ", rel10, "\n");
        Print("  Relation gExt^fExt32 = gExt^4  ? ", rel4, "\n");

        if rel10 then
            Add(GoodGExt10Lines32, [i, KacLines10_32[i]]);
        fi;

    fi;

od;

############################################################
# PART 5. Test regular exponent-4 lines
############################################################

Print("\nTesting regular exponent-4 Kac lines.\n");

GoodGExt4Lines32 := [];;

for i in [1..Length(KacLines4_32)] do

    counts := ResidueCountsForLine32(KacLines4_32[i]);

    if counts[1] = 0 then

        gExt := BuildGExtFromKacLine32(KacLines4_32[i]);

        Print("\nExponent-4 regular line ", i, ": ",
              KacLines4_32[i], "\n");

        Print("  gExt^13 = identity? ", gExt^13 = Id52K13_32, "\n");
        Print("  gExt = identity? ", gExt = Id52K13_32, "\n");
        Print("  Trace(gExt) = ", TraceMat(gExt), "\n");

        rel10 := (gExt^fExt32 = gExt^10);
        rel4  := (gExt^fExt32 = gExt^4);

        Print("  Relation gExt^fExt32 = gExt^10 ? ", rel10, "\n");
        Print("  Relation gExt^fExt32 = gExt^4  ? ", rel4, "\n");

        if rel4 then
            Add(GoodGExt4Lines32, [i, KacLines4_32[i]]);
        fi;

    fi;

od;

############################################################
# PART 6. Summary
############################################################

Print("\n============================================================\n");
Print("SUMMARY OF EXTENSION-FIELD TORUS TEST\n");
Print("============================================================\n");

Print("Good exponent-10 extension-field lines:\n");
Print(GoodGExt10Lines32, "\n");

Print("Good exponent-4 extension-field lines:\n");
Print(GoodGExt4Lines32, "\n");

if Length(GoodGExt10Lines32) > 0 then
    chosenLineIndex32 := GoodGExt10Lines32[1][1];;
    chosenKacLine32 := GoodGExt10Lines32[1][2];;
    gExt32 := BuildGExtFromKacLine32(chosenKacLine32);;

    Print("\nChosen exponent-10 line:\n");
    Print("  index = ", chosenLineIndex32, "\n");
    Print("  line  = ", chosenKacLine32, "\n");

    Print("Stored gExt32 over GF(7^12).\n");
elif Length(GoodGExt4Lines32) > 0 then
    chosenLineIndex32 := GoodGExt4Lines32[1][1];;
    chosenKacLine32 := GoodGExt4Lines32[1][2];;
    gExt32 := BuildGExtFromKacLine32(chosenKacLine32);;

    Print("\nChosen exponent-4 line:\n");
    Print("  index = ", chosenLineIndex32, "\n");
    Print("  line  = ", chosenKacLine32, "\n");
    Print("This gives exponent 4 for f32B, so exponent 10 for f32B^-1.\n");

    Print("Stored gExt32 over GF(7^12).\n");
else
    Print("\nNo extension-field relation verified. Check convention.\n");
fi;

Print("\n============================================================\n");
Print("STEP 36 FINISHED\n");
Print("============================================================\n");

############################################################
# STEP 36C:
# Order distribution inside extension-field B=<gExt32,fExt32>
############################################################

Print("\n============================================================\n");
Print("STEP 36C: ORDER DISTRIBUTION IN B=<gExt32,fExt32>\n");
Print("============================================================\n");

OrderDistribution32 := function(L)
    local counts, x, ox, pos;

    counts := [];

    for x in L do
        ox := Order(x);
        pos := PositionProperty(counts, p -> p[1] = ox);

        if pos = fail then
            Add(counts, [ox, 1]);
        else
            counts[pos][2] := counts[pos][2] + 1;
        fi;
    od;

    SortBy(counts, p -> p[1]);
    return counts;
end;;

BExtElements32 := [];;

for i in [0..12] do
    for j in [0..5] do
        Add(BExtElements32, gExt32^i * fExt32^j);
    od;
od;

distBExt32 := OrderDistribution32(BExtElements32);;

Print("Order distribution in BExt=<gExt32,fExt32>:\n");

for pair in distBExt32 do
    Print("  order ", pair[1], " : ", pair[2], "\n");
od;

Print("\nExpected for 13:6:\n");
Print("  order 1  : 1\n");
Print("  order 2  : 13\n");
Print("  order 3  : 26\n");
Print("  order 6  : 26\n");
Print("  order 13 : 12\n");

Print("\n============================================================\n");
Print("STEP 36C FINISHED\n");
Print("============================================================\n");

############################################################
# OPTIONAL SLOW STEP 37A:
# Weyl-lift extended-centraliser search for Walton t
#
# This original version is preserved but disabled by default, because it
# tests extension-field Bruhat witnesses inside the full enumeration loop.
# The practical route is:
#
#       Step 37A FAST -> Step 37B -> Step 37C -> Step 37D.
############################################################

if RUN_SLOW_STEP_37A_FULL_32 then

Print("\n============================================================\n");
Print("SLOW STEP 37A: WEYL-LIFT EXTENDED-CENTRALISER SEARCH FOR t\n");
Print("============================================================\n");

if not IsBound(f32B) then
    Error("f32B is not bound.\n");
fi;

if not IsBound(fExt32) then
    Error("fExt32 is not bound.\n");
fi;

if not IsBound(gExt32) then
    Error("gExt32 is not bound.\n");
fi;

if not IsBound(WeylLifts32) then
    Error("WeylLifts32 is not bound.\n");
fi;

if not IsBound(Id52K13_32) then
    Id52K13_32 := IdentityMat(52, K13_32);;
fi;

trace_t_target := -4 * One(F32);;

Print("Order(gExt32) = ", Order(gExt32), "\n");
Print("Order(fExt32) = ", Order(fExt32), "\n");
Print("Check gExt32^fExt32 = gExt32^10 ? ",
      gExt32^fExt32 = gExt32^10, "\n");

Print("Target trace for t is -4 = ", trace_t_target, " in GF(7)\n");

BExtElements32 := [];;

for i in [0..12] do
    for j in [0..5] do
        Add(BExtElements32, gExt32^i * fExt32^j);
    od;
od;

Print("Built BExtElements32 with length ", Length(BExtElements32), "\n");

IsInMatrixList32 := function(x, L)
    return ForAny(L, y -> x = y);
end;;

ActionExponentOnGExt32 := function(t)
    local image, k;

    image := gExt32^t;

    for k in [1..12] do
        if image = gExt32^k then
            return k;
        fi;
    od;

    return fail;
end;;

HasBruhatOrder3Witness32 := function(tExt)
    local b, bt, witnesses;

    witnesses := [];

    for b in BExtElements32 do

        bt := b * tExt;

        # Avoid expensive Order(bt). Just test exact order 3.
        if bt <> Id52K13_32 and bt^3 = Id52K13_32 then
            Add(witnesses, b);
        fi;

    od;

    return witnesses;
end;;

Print("\nBuilding Wlift32 := Group(WeylLifts32).\n");
Print("This is the small Weyl-lift subgroup, not full G32B.\n");

Wlift32 := Group(WeylLifts32);;

Print("Constructed Wlift32.\n");
Print("Number of generators = ", Length(GeneratorsOfGroup(Wlift32)), "\n");

sizeWlift32 := Size(Wlift32);;

Print("Size(Wlift32) = ", sizeWlift32, "\n");

if sizeWlift32 > 200000 then
    Error("Wlift32 is larger than expected. Stop before enumeration.\n");
fi;

Print("\nEnumerating Wlift32 elements.\n");

WliftElements32 := Elements(Wlift32);;

Print("Number of Weyl-lift elements enumerated = ",
      Length(WliftElements32), "\n");

exactInverters32 := [];;
traceMinus4ExactInverters32 := [];;
goodTWeylCandidates32 := [];;

traceDistExactInverters32 := [];;

IncrementCount37A := function(counts, value)
    local pos;

    pos := PositionProperty(counts, p -> p[1] = value);

    if pos = fail then
        Add(counts, [value, 1]);
    else
        counts[pos][2] := counts[pos][2] + 1;
    fi;
end;;

for t32 in WliftElements32 do

    if Order(t32) = 2 then

        if f32B^t32 = f32B^-1 then

            Add(exactInverters32, t32);
            IncrementCount37A(traceDistExactInverters32, Trace32(t32));

            if Trace32(t32) = trace_t_target then

                Add(traceMinus4ExactInverters32, t32);

                tExt := LiftMatrixToK13_32(t32);

                expOnG := ActionExponentOnGExt32(tExt);
                inB := IsInMatrixList32(tExt, BExtElements32);
                witnesses := HasBruhatOrder3Witness32(tExt);

                if expOnG = fail and not inB and Length(witnesses) > 0 then
                    Add(goodTWeylCandidates32,
                        [t32, tExt, Length(witnesses)]);
                fi;

            fi;

        fi;

    fi;

od;

Print("\n============================================================\n");
Print("REPORT: SLOW WEYL-LIFT EXTENDED-CENTRALISER SEARCH\n");
Print("============================================================\n");

Print("Number of exact inverting Weyl-lift involutions = ",
      Length(exactInverters32), "\n");

Print("\nTrace distribution among exact inverting Weyl-lift involutions:\n");

SortBy(traceDistExactInverters32, p -> String(p[1]));

for pair in traceDistExactInverters32 do
    Print("  trace ", pair[1], " : ", pair[2], "\n");
od;

Print("\nNumber of exact inverters with trace -4 = ",
      Length(traceMinus4ExactInverters32), "\n");

Print("Number of Weyl-lift candidates also satisfying external Bruhat tests = ",
      Length(goodTWeylCandidates32), "\n");

if Length(goodTWeylCandidates32) > 0 then

    Print("\nSUCCESS: found Weyl-lift Walton t candidate(s).\n");

    t32B := goodTWeylCandidates32[1][1];;
    tExt32 := goodTWeylCandidates32[1][2];;

    Print("Stored t32B and tExt32.\n");
    Print("Order(t32B) = ", Order(t32B), "\n");
    Print("Trace(t32B) = ", Trace32(t32B), "\n");
    Print("f32B^t32B = f32B^-1 ? ", f32B^t32B = f32B^-1, "\n");
    Print("Action exponent on <gExt32> = ",
          ActionExponentOnGExt32(tExt32), "\n");
    Print("Number of Bruhat order-3 witnesses b in B = ",
          goodTWeylCandidates32[1][3], "\n");

else

    Print("\nNo Weyl-lift t candidate found in slow Step 37A.\n");
    Print("Use Step 37A FAST + 37B/C/D for the practical route.\n");

fi;

Print("\n============================================================\n");
Print("SLOW STEP 37A FINISHED\n");
Print("============================================================\n");

fi;

############################################################
# STEP 37A FAST:
# Fast Weyl-lift exact-inverter scan
#
# This replaces the slow loop using Order(t32).
#
# It only checks:
#   t^2 = 1
#   t != 1
#   f32B^t = f32B^-1
#   Trace(t)
#
# No extension-field Bruhat test yet.
############################################################

Print("\n============================================================\n");
Print("STEP 37A FAST: WEYL-LIFT EXACT-INVERTER TRACE SCAN\n");
Print("============================================================\n");

Id52F7_32 := IdentityMat(52, F32);;

trace_t_target := -4 * One(F32);;

Print("Target trace -4 in GF(7) = ", trace_t_target, "\n");

if not IsBound(WliftElements32) then
    Print("WliftElements32 not bound, rebuilding Wlift32.\n");
    Wlift32 := Group(WeylLifts32);;
    Print("Size(Wlift32) = ", Size(Wlift32), "\n");
    WliftElements32 := Elements(Wlift32);;
fi;

Print("Length(WliftElements32) = ", Length(WliftElements32), "\n");

exactInvertersFast32 := [];;
traceMinus4ExactInvertersFast32 := [];;
traceDistExactInvertersFast32 := [];;

IncrementCount37AFast := function(counts, value)
    local pos;

    pos := PositionProperty(counts, p -> p[1] = value);

    if pos = fail then
        Add(counts, [value, 1]);
    else
        counts[pos][2] := counts[pos][2] + 1;
    fi;
end;;

checked37A := 0;;
involutions37A := 0;;

for t32 in WliftElements32 do

    checked37A := checked37A + 1;

    # Fast involution test:
    # instead of Order(t32)=2
    if t32 <> Id52F7_32 and t32^2 = Id52F7_32 then

        involutions37A := involutions37A + 1;

        if f32B^t32 = f32B^-1 then

            Add(exactInvertersFast32, t32);
            tr := Trace32(t32);
            IncrementCount37AFast(traceDistExactInvertersFast32, tr);

            if tr = trace_t_target then
                Add(traceMinus4ExactInvertersFast32, t32);
            fi;

        fi;

    fi;

    if checked37A mod 2000 = 0 then
        Print("Checked ", checked37A, " / ", Length(WliftElements32),
              "; involutions so far = ", involutions37A,
              "; exact inverters so far = ", Length(exactInvertersFast32),
              "; trace -4 exact inverters so far = ",
              Length(traceMinus4ExactInvertersFast32), "\n");
    fi;

od;

SortBy(traceDistExactInvertersFast32, p -> String(p[1]));

Print("\n============================================================\n");
Print("REPORT: STEP 37A FAST\n");
Print("============================================================\n");

Print("Total checked = ", checked37A, "\n");
Print("Total involutions found = ", involutions37A, "\n");
Print("Exact inverters of f32B = ", Length(exactInvertersFast32), "\n");
Print("Exact inverters with trace -4 = ",
      Length(traceMinus4ExactInvertersFast32), "\n");

Print("\nTrace distribution among exact inverters:\n");
for pair in traceDistExactInvertersFast32 do
    Print("  trace ", pair[1], " : ", pair[2], "\n");
od;

if Length(traceMinus4ExactInvertersFast32) = 0 then
    Print("\nConclusion:\n");
    Print("No trace -4 exact-inverting t inside the pure Weyl-lift subgroup.\n");
    Print("So the real Walton t is not pure Weyl-lift. Next step should use root-group/centraliser data.\n");
else
    Print("\nThere are trace -4 exact inverters inside Wlift32.\n");
    Print("Next step: test only these few candidates over GF(7^12) for Bruhat order-3 witnesses.\n");
fi;

Print("\n============================================================\n");
Print("STEP 37A FAST FINISHED\n");
Print("============================================================\n");

############################################################
# STEP 37B:
# Test the 36 trace -4 exact-inverting Weyl-lift candidates
# over GF(7^12), but WITHOUT Bruhat witnesses yet.
#
# We check:
#   tExt^2 = 1
#   fExt32^tExt = fExt32^-1
#   tExt not in BExt
#   tExt does not normalise <gExt32>
#
# This is a safe filter before expensive Bruhat tests.
############################################################

Print("\n============================================================\n");
Print("STEP 37B: BASIC TESTS FOR 36 EXACT-INVERTING t CANDIDATES\n");
Print("============================================================\n");

if not IsBound(traceMinus4ExactInvertersFast32) then
    Error("traceMinus4ExactInvertersFast32 is not bound. Run Step 37A FAST first.\n");
fi;

if not IsBound(BExtElements32) then
    BExtElements32 := [];;

    for i in [0..12] do
        for j in [0..5] do
            Add(BExtElements32, gExt32^i * fExt32^j);
        od;
    od;
fi;

if not IsBound(Id52K13_32) then
    Id52K13_32 := IdentityMat(52, K13_32);;
fi;

IsInMatrixList32 := function(x, L)
    return ForAny(L, y -> x = y);
end;;

ActionExponentOnGExt32 := function(t)
    local image, k;

    image := gExt32^t;

    for k in [1..12] do
        if image = gExt32^k then
            return k;
        fi;
    od;

    return fail;
end;;

GoodTBasicCandidates32 := [];;

Print("Number of trace -4 exact-inverting candidates to test = ",
      Length(traceMinus4ExactInvertersFast32), "\n");

for idx in [1..Length(traceMinus4ExactInvertersFast32)] do

    t32 := traceMinus4ExactInvertersFast32[idx];;
    tExt := LiftMatrixToK13_32(t32);;

    isInv := (tExt^2 = Id52K13_32 and tExt <> Id52K13_32);
    invertsF := (fExt32^tExt = fExt32^-1);
    expOnG := ActionExponentOnGExt32(tExt);
    inB := IsInMatrixList32(tExt, BExtElements32);

    Print("\nCandidate ", idx, ":\n");
    Print("  tExt^2=1 and tExt<>1? ", isInv, "\n");
    Print("  fExt32^tExt = fExt32^-1? ", invertsF, "\n");
    Print("  action exponent on <gExt32> = ", expOnG, "\n");
    Print("  tExt in BExt? ", inB, "\n");

    if isInv and invertsF and expOnG = fail and not inB then
        Add(GoodTBasicCandidates32, [idx, t32, tExt]);
        Print("  BASIC STATUS: good external-type candidate\n");
    else
        Print("  BASIC STATUS: rejected by basic filter\n");
    fi;

od;

Print("\n============================================================\n");
Print("REPORT STEP 37B\n");
Print("============================================================\n");

Print("Number passing basic external-type filter = ",
      Length(GoodTBasicCandidates32), "\n");

if Length(GoodTBasicCandidates32) > 0 then
    Print("Good candidate indices:\n");
    for x in GoodTBasicCandidates32 do
        Print("  candidate ", x[1], "\n");
    od;
else
    Print("No candidate passed the basic external-type filter.\n");
fi;

Print("\n============================================================\n");
Print("STEP 37B FINISHED\n");
Print("============================================================\n");

############################################################
# STEP 37C:
# Bruhat/order-3 test for the 36 external-type t candidates
#
# First test the six witness patterns found in abstract PSL2(13):
#
#   b = g^12 f^3
#   b = g^9  f^4
#   b = g^10 f^5
#   b = g^1  f^0
#   b = g^4  f^1
#   b = g^3  f^2
#
# For each candidate t, test:
#
#   (b*t)^3 = 1 and b*t != 1.
#
# This is much cheaper than testing all 78 b's first.
############################################################

Print("\n============================================================\n");
Print("STEP 37C: BRUHAT TEST USING ABSTRACT PSL2(13) WITNESS PAIRS\n");
Print("============================================================\n");

if not IsBound(GoodTBasicCandidates32) then
    Error("GoodTBasicCandidates32 is not bound. Run Step 37B first.\n");
fi;

if not IsBound(Id52K13_32) then
    Id52K13_32 := IdentityMat(52, K13_32);;
fi;

AbstractWitnessPairs32 := [
    [12,3],
    [9,4],
    [10,5],
    [1,0],
    [4,1],
    [3,2]
];;

GoodTBruhatWitnesses32 := [];;

Print("Number of external-type t candidates = ",
      Length(GoodTBasicCandidates32), "\n");

Print("Testing abstract witness pairs:\n");
for p in AbstractWitnessPairs32 do
    Print("  g^", p[1], " * f^", p[2], "\n");
od;

for cand in GoodTBasicCandidates32 do

    candIndex := cand[1];;
    t32 := cand[2];;
    tExt := cand[3];;

    Print("\nTesting t candidate ", candIndex, "\n");

    for pair in AbstractWitnessPairs32 do

        i := pair[1];;
        j := pair[2];;

        b := gExt32^i * fExt32^j;;
        bt := b * tExt;;

        if bt <> Id52K13_32 and bt^3 = Id52K13_32 then

            Print("  SUCCESS: Bruhat witness found!\n");
            Print("  t candidate = ", candIndex, "\n");
            Print("  witness b = g^", i, " * f^", j, "\n");

            Add(GoodTBruhatWitnesses32, [candIndex, i, j, t32, tExt]);

        fi;

    od;

od;

Print("\n============================================================\n");
Print("REPORT STEP 37C\n");
Print("============================================================\n");

Print("Number of Bruhat hits using abstract witness pairs = ",
      Length(GoodTBruhatWitnesses32), "\n");

if Length(GoodTBruhatWitnesses32) > 0 then

    Print("\nSUCCESS: found Walton-style Bruhat t candidate(s).\n");

    for x in GoodTBruhatWitnesses32 do
        Print("  candidate ", x[1],
              " with witness b = g^", x[2],
              " * f^", x[3], "\n");
    od;

    t32B := GoodTBruhatWitnesses32[1][4];;
    tExt32 := GoodTBruhatWitnesses32[1][5];;

    Print("\nStored first successful candidate as t32B and tExt32.\n");
    Print("Order(t32B) = ", Order(t32B), "\n");
    Print("Trace(t32B) = ", Trace32(t32B), "\n");
    Print("f32B^t32B = f32B^-1 ? ", f32B^t32B = f32B^-1, "\n");

else

    Print("\nNo hit among the six abstract witness pairs.\n");
    Print("This does not mean failure.\n");
    Print("Next step: test all 78 elements b=g^i f^j in BExt.\n");

fi;

Print("\n============================================================\n");
Print("STEP 37C FINISHED\n");
Print("============================================================\n");

############################################################
# STEP 37D:
# Full Bruhat/order-3 test for all 78 b in BExt
#
# We now test every:
#
#       b = gExt32^i * fExt32^j
#
# for:
#
#       (b*tExt)^3 = 1 and b*tExt != 1.
#
# This is the real Bruhat test.
############################################################

Print("\n============================================================\n");
Print("STEP 37D: FULL BRUHAT TEST OVER ALL 78 ELEMENTS OF BExt\n");
Print("============================================================\n");

if not IsBound(GoodTBasicCandidates32) then
    Error("GoodTBasicCandidates32 is not bound. Run Step 37B first.\n");
fi;

if not IsBound(Id52K13_32) then
    Id52K13_32 := IdentityMat(52, K13_32);;
fi;

############################################################
# PART 1. Build labelled B-elements
############################################################

BExtLabelledElements32 := [];;

for i in [0..12] do
    for j in [0..5] do
        Add(BExtLabelledElements32,
            [i, j, gExt32^i * fExt32^j]);
    od;
od;

Print("Number of labelled BExt elements = ",
      Length(BExtLabelledElements32), "\n");

############################################################
# PART 2. Full Bruhat test
############################################################

GoodTFullBruhatWitnesses32 := [];;

Print("Number of t candidates to test = ",
      Length(GoodTBasicCandidates32), "\n");

for cand in GoodTBasicCandidates32 do

    candIndex := cand[1];;
    t32 := cand[2];;
    tExt := cand[3];;

    Print("\nTesting t candidate ", candIndex, " against all 78 b-elements.\n");

    hitsForThisT := [];;

    for labelledB in BExtLabelledElements32 do

        i := labelledB[1];;
        j := labelledB[2];;
        b := labelledB[3];;

        bt := b * tExt;;

        if bt <> Id52K13_32 and bt^3 = Id52K13_32 then

            Print("  HIT: b = g^", i, " * f^", j,
                  " gives (b*t)^3=1.\n");

            Add(hitsForThisT, [i,j]);

        fi;

    od;

    if Length(hitsForThisT) > 0 then

        Add(GoodTFullBruhatWitnesses32,
            [candIndex, hitsForThisT, t32, tExt]);

        Print("  Candidate ", candIndex,
              " has ", Length(hitsForThisT),
              " Bruhat witness(es).\n");

    else

        Print("  Candidate ", candIndex,
              " has no Bruhat witness in BExt.\n");

    fi;

od;

############################################################
# PART 3. Report
############################################################

Print("\n============================================================\n");
Print("REPORT STEP 37D\n");
Print("============================================================\n");

Print("Number of t candidates with at least one Bruhat witness = ",
      Length(GoodTFullBruhatWitnesses32), "\n");

if Length(GoodTFullBruhatWitnesses32) > 0 then

    Print("\nSUCCESS: found Walton-style Bruhat t candidate(s).\n");

    for entry in GoodTFullBruhatWitnesses32 do

        Print("\nCandidate ", entry[1], " witnesses:\n");

        for pair in entry[2] do
            Print("  b = g^", pair[1], " * f^", pair[2], "\n");
        od;

    od;

    t32B := GoodTFullBruhatWitnesses32[1][3];;
    tExt32 := GoodTFullBruhatWitnesses32[1][4];;

    Print("\nStored first successful candidate as t32B and tExt32.\n");

    Print("\nChecks for stored t:\n");
    Print("Order(t32B) = ", Order(t32B), "\n");
    Print("Trace(t32B) = ", Trace32(t32B), "\n");
    Print("f32B^t32B = f32B^-1 ? ", f32B^t32B = f32B^-1, "\n");
    Print("tExt32^2 = identity? ", tExt32^2 = Id52K13_32, "\n");
    Print("tExt32 in BExt? ",
          ForAny(BExtElements32, x -> x = tExt32), "\n");

else

    Print("\nNo Bruhat hit for current gExt32 and these Weyl-lift exact inverters.\n");
    Print("This would mean: exact-inverting Weyl-lift t's exist, but none gives the order-3 Bruhat relation for this chosen Kac line.\n");
    Print("Next step would be to repeat this full test for the other regular exponent-4/Kac lines.\n");

fi;

Print("\n============================================================\n");
Print("STEP 37D FINISHED\n");
Print("============================================================\n");

############################################################
# FINAL SUMMARY BLOCK
############################################################

Print("\n============================================================\n");
Print("FINAL SUMMARY: STRUCTURAL F4(7) WALTON SEARCH SCRIPT FINISHED\n");
Print("============================================================\n");

Print("Key objects available if construction reached them:\n");
Print("  F32                  = GF(7)\n");
Print("  L32                  = L(F4) over GF(7)\n");
Print("  BAS32                = 52-dimensional Chevalley basis\n");
Print("  G32B                 = adjoint root-group-generated F4(7)-type group\n");
Print("  WeylLifts32          = root-reflection lifts\n");
Print("  f32B                 = fixed structural order-6 matrix over GF(7)\n");
Print("  fExt32               = lift of f32B to GF(7^12)\n");
Print("  KacLines10_32        = Kac-residue lines with exponent 10\n");
Print("  KacLines4_32         = Kac-residue lines with exponent 4\n");
Print("  gExt32               = chosen extension-field order-13 torus element\n");
Print("  BExtElements32       = 78 normal-form elements g^i f^j\n");
Print("  traceMinus4ExactInvertersFast32 = trace -4 exact-inverting Weyl-lift t candidates\n");
Print("  GoodTBasicCandidates32          = external-type t candidates\n");
Print("  GoodTBruhatWitnesses32          = abstract-pair Bruhat hits, if any\n");
Print("  GoodTFullBruhatWitnesses32      = full 78-element Bruhat hits, if any\n");

Print("\nDone.\n");
Print("============================================================\n");
