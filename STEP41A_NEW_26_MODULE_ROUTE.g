############################################################
# STEP 41A:
# NEW METHOD FROM MEETING
#
# New direction:
#   Stop the pure Weyl-lift t search for now.
#   Start the 26-dimensional minimal F4 module route.
#
# Background from previous work:
#   The adjoint 52-dimensional route successfully built the local
#   subgroup B = <g,f> of shape 13:6.
#   It also found 36 trace -4 Weyl-lift involutions t satisfying
#   f^t = f^-1.
#   But the full Bruhat/order-3 test gave no hits for pure Weyl-lift t.
#
# New idea:
#   Work with the 26-dimensional minimal F4 module.
#   Expected restriction:
#
#       V26 down to PSL2(13) should contain a 12-dimensional piece
#       and a 14-dimensional piece.
#
#   This script starts the representation-level model:
#
#   1. Build the abstract PSL2(13) fingerprint.
#   2. Build the 12-dimensional module from the 14-point action.
#   3. Keep the full 14-point permutation module as a reference only.
#   4. Check whether this OSCAR/GAP installation can construct the
#      26-dimensional minimal F4 module directly.
#
# Paste this at gap> after:
#
#   using Oscar
#   GAP.prompt()
#
############################################################

LogTo("STEP41A_NEW_26_MODULE_ROUTE_LOG.txt");

Print("\n============================================================\n");
Print("STEP 41A: START NEW 26-DIMENSIONAL MODULE METHOD\n");
Print("============================================================\n");

LoadPackage("ctbllib");
LoadPackage("sla");

F7_41 := GF(7);;
one7_41 := One(F7_41);;
zero7_41 := Zero(F7_41);;

trace_g_target_41  := zero7_41;;
trace_f_target_41  := 2 * one7_41;;
trace_f2_target_41 := 5 * one7_41;;
trace_f3_target_41 := 3 * one7_41;;
trace_t_target_41  := 3 * one7_41;;

Print("\nField is GF(7).\n");
Print("Trace targets in GF(7):\n");
Print("  trace(g)   should be 0\n");
Print("  trace(f)   should be 2\n");
Print("  trace(f^2) should be 5, meaning -2\n");
Print("  trace(f^3) should be 3, meaning -4\n");
Print("  trace(t)   should be 3, meaning -4\n");


############################################################
# PART 1. Abstract PSL2(13) local fingerprint
############################################################

Print("\n------------------------------------------------------------\n");
Print("PART 1: ABSTRACT PSL2(13) FINGERPRINT\n");
Print("------------------------------------------------------------\n");

H41 := PSL(2,13);;

Print("Size(H41) = ", Size(H41), "\n");

ActionExponentCyclic41 := function(g, x)
    local gx, k;

    gx := g^x;

    for k in [0..Order(g)-1] do
        if gx = g^k then
            return k;
        fi;
    od;

    return fail;
end;;

FindBruhatWitness41 := function(g, f, t)
    local i, j, b;

    for i in [0..12] do
        for j in [0..5] do
            b := g^i * f^j;

            if b*t <> One(Parent(H41, b*t)) and Order(b*t) = 3 then
                return rec(i := i, j := j, b := b);
            fi;
        od;
    od;

    return fail;
end;;

# Choose g of order 13.
g41 := First(Elements(H41), x -> Order(x) = 13);;
P41 := Group(g41);;
NP41 := Normalizer(H41, P41);;

Print("Order(g41) = ", Order(g41), "\n");
Print("Size(N_H(<g41>)) = ", Size(NP41), "\n");

# Choose f of order 6 acting on <g> by exponent 10.
f41 := fail;;

for x in Elements(NP41) do
    if Order(x) = 6 then
        if ActionExponentCyclic41(g41, x) = 10 then
            f41 := x;
            break;
        elif ActionExponentCyclic41(g41, x) = 4 then
            f41 := x^-1;
            break;
        fi;
    fi;
od;

if f41 = fail then
    Error("Could not find f41 of order 6 acting by exponent 10.");
fi;

B41 := Group(g41, f41);;

Print("Order(f41) = ", Order(f41), "\n");
Print("Action exponent of f41 on <g41> = ",
      ActionExponentCyclic41(g41, f41), "\n");
Print("Size(B41=<g41,f41>) = ", Size(B41), "\n");

# Find exact-inverting external t in abstract PSL2(13).
GoodT41 := [];;

for t in Elements(H41) do
    if Order(t) = 2 then
        if f41^t = f41^-1 then
            if not (t in B41) then
                if ActionExponentCyclic41(g41, t) = fail then
                    Add(GoodT41, t);
                fi;
            fi;
        fi;
    fi;
od;

Print("Number of abstract external exact-inverting t candidates = ",
      Length(GoodT41), "\n");

if Length(GoodT41) = 0 then
    Error("No abstract external exact-inverting t candidates found.");
fi;

t41 := GoodT41[1];;
wit41 := FindBruhatWitness41(g41, f41, t41);;

Print("Chosen t41 has order = ", Order(t41), "\n");
Print("f41^t41 = f41^-1 ? ", f41^t41 = f41^-1, "\n");
Print("t41 normalises <g41>? ",
      ActionExponentCyclic41(g41, t41) <> fail, "\n");
Print("t41 in B41? ", t41 in B41, "\n");

if wit41 = fail then
    Print("No Bruhat witness found for chosen t41.\n");
else
    Print("Bruhat witness found: b = g^", wit41.i,
          " * f^", wit41.j, "\n");
    Print("Order(b*t41) = ", Order(wit41.b * t41), "\n");
fi;

Print("Size(<g41,f41,t41>) = ", Size(Group(g41, f41, t41)), "\n");


############################################################
# PART 2. Build the 12-dimensional module from the 14-point action
#
# We use B41 as a point stabiliser.
# The coset action has degree 14.
#
# In characteristic 7, the 14-point permutation module has a
# fixed line inside the augmentation submodule.
#
# The 12-dimensional quotient is:
#
#   augmentation submodule / fixed line
#
# This gives the important 12-dimensional piece for the new
# 26-dimensional method.
############################################################

Print("\n------------------------------------------------------------\n");
Print("PART 2: BUILD THE 12-DIMENSIONAL MODULE\n");
Print("------------------------------------------------------------\n");

cosets41 := RightCosets(H41, B41);;
hom14_41 := ActionHomomorphism(H41, cosets41, OnRight);;

Print("Degree of coset action = ", Length(cosets41), "\n");

Perm14Of41 := function(x)
    return Image(hom14_41, x);
end;;

TraceSmall41 := function(M)
    local s, i;

    s := Zero(M[1][1]);

    for i in [1..Length(M)] do
        s := s + M[i][i];
    od;

    return s;
end;;

# Full 14-dimensional permutation matrix.
# This is kept only as a reference. It is not automatically the final
# irreducible 14-dimensional piece needed inside V26.
Mat14FromPerm41 := function(p)
    local M, i;

    M := NullMat(14, 14, F7_41);

    for i in [1..14] do
        M[i^p][i] := one7_41;
    od;

    return M;
end;;

# Matrix for the 12-dimensional quotient.
#
# Basis:
#   u_1, ..., u_12
#
# where:
#   u_i = e_i - e_14
#
# and:
#   u_13 = -u_1 - ... - u_12
#
# This implements the quotient of the augmentation submodule by the
# fixed line.
Mat12FromPerm41 := function(p)
    local cols, i, vec, a, b, r, col, M;

    cols := [];

    for i in [1..12] do
        vec := List([1..14], k -> zero7_41);

        a := i^p;
        b := 14^p;

        vec[a] := vec[a] + one7_41;
        vec[b] := vec[b] - one7_41;

        col := [];

        for r in [1..12] do
            Add(col, vec[r] - vec[13]);
        od;

        Add(cols, col);
    od;

    M := TransposedMat(cols);

    return M;
end;;

g14perm_41 := Mat14FromPerm41(Perm14Of41(g41));;
f14perm_41 := Mat14FromPerm41(Perm14Of41(f41));;
t14perm_41 := Mat14FromPerm41(Perm14Of41(t41));;

G14perm_41 := Group(g14perm_41, f14perm_41, t14perm_41);;
B14perm_41 := Group(g14perm_41, f14perm_41);;

Print("\nReference 14-point permutation module:\n");
Print("Order(g14perm_41) = ", Order(g14perm_41), "\n");
Print("Order(f14perm_41) = ", Order(f14perm_41), "\n");
Print("Order(t14perm_41) = ", Order(t14perm_41), "\n");
Print("Trace(g14perm_41) = ", TraceSmall41(g14perm_41), "\n");
Print("Trace(f14perm_41) = ", TraceSmall41(f14perm_41), "\n");
Print("Trace(f14perm_41^2) = ", TraceSmall41(f14perm_41^2), "\n");
Print("Trace(f14perm_41^3) = ", TraceSmall41(f14perm_41^3), "\n");
Print("Trace(t14perm_41) = ", TraceSmall41(t14perm_41), "\n");
Print("Size(<g14perm_41,f14perm_41>) = ", Size(B14perm_41), "\n");
Print("Size(<g14perm_41,f14perm_41,t14perm_41>) = ", Size(G14perm_41), "\n");

g12_41 := Mat12FromPerm41(Perm14Of41(g41));;
f12_41 := Mat12FromPerm41(Perm14Of41(f41));;
t12_41 := Mat12FromPerm41(Perm14Of41(t41));;

G12_41 := Group(g12_41, f12_41, t12_41);;
B12_41 := Group(g12_41, f12_41);;

Print("\nThe 12-dimensional quotient module:\n");
Print("Order(g12_41) = ", Order(g12_41), "\n");
Print("Order(f12_41) = ", Order(f12_41), "\n");
Print("Order(t12_41) = ", Order(t12_41), "\n");

Print("Trace(g12_41) = ", TraceSmall41(g12_41), "\n");
Print("Trace(f12_41) = ", TraceSmall41(f12_41), "\n");
Print("Trace(f12_41^2) = ", TraceSmall41(f12_41^2), "\n");
Print("Trace(f12_41^3) = ", TraceSmall41(f12_41^3), "\n");
Print("Trace(t12_41) = ", TraceSmall41(t12_41), "\n");

Print("Size(<g12_41,f12_41>) = ", Size(B12_41), "\n");
Print("Size(<g12_41,f12_41,t12_41>) = ", Size(G12_41), "\n");

wit12_41 := fail;;

for i in [0..12] do
    for j in [0..5] do
        b12_41 := g12_41^i * f12_41^j;

        if b12_41*t12_41 <> IdentityMat(12, F7_41)
           and Order(b12_41*t12_41) = 3 then
            wit12_41 := rec(i := i, j := j);
            break;
        fi;
    od;

    if wit12_41 <> fail then
        break;
    fi;
od;

if wit12_41 = fail then
    Print("No 12-dimensional Bruhat witness found.\n");
else
    Print("12-dimensional Bruhat witness: b = g^",
          wit12_41.i, " * f^", wit12_41.j, "\n");
fi;


############################################################
# PART 3. Check the Brauer table expectation
#
# This part verifies the representation-level target from the
# Brauer table of PSL2(13) in characteristic 7.
#
# We want to keep the new direction tied to character data:
#   V26 should have a 12-dimensional part and a 14-dimensional part.
############################################################

Print("\n------------------------------------------------------------\n");
Print("PART 3: BRAUER TABLE CHECK FOR PSL2(13) IN CHARACTERISTIC 7\n");
Print("------------------------------------------------------------\n");

tbl41 := CharacterTable("L2(13)");;

if tbl41 = fail then
    tbl41 := CharacterTable("PSL(2,13)");
fi;

if tbl41 = fail then
    Print("Could not load character table for L2(13).\n");
else
    btbl41 := BrauerTable(tbl41, 7);;

    if btbl41 = fail then
        Print("Could not load Brauer table for L2(13) in characteristic 7.\n");
    else
        irr41 := Irr(btbl41);;
        orders41 := OrdersClassRepresentatives(btbl41);;
        degrees41 := List(irr41, chi -> chi[1]);;

        Print("Brauer class orders = ", orders41, "\n");
        Print("Brauer irreducible degrees = ", degrees41, "\n");

        pos13_41 := Positions(orders41, 13);;
        pos2_41 := Positions(orders41, 2);;
        pos3_41 := Positions(orders41, 3);;
        pos6_41 := Positions(orders41, 6);;

        Print("Positions of order-13 classes = ", pos13_41, "\n");
        Print("Positions of order-2 classes = ", pos2_41, "\n");
        Print("Positions of order-3 classes = ", pos3_41, "\n");
        Print("Positions of order-6 classes = ", pos6_41, "\n");

        Print("\nIrreducible Brauer characters:\n");

        for k41 in [1..Length(irr41)] do
            Print("  number ", k41,
                  " degree ", irr41[k41][1],
                  " values ", irr41[k41], "\n");
        od;
    fi;
fi;


############################################################
# PART 4. Check whether this installation can build the
# 26-dimensional minimal F4 module directly.
#
# Important:
#   SimpleLieAlgebra("F",4,F7) builds the 52-dimensional Lie algebra.
#   That is the adjoint module, not the 26-dimensional minimal module.
#
# Here we only check whether useful constructors exist.
############################################################

Print("\n------------------------------------------------------------\n");
Print("PART 4: TRY TO BUILD THE 26-DIMENSIONAL F4 MODULE\n");
Print("------------------------------------------------------------\n");

Print("Checking useful constructors:\n");

for name41 in [
    "SimpleLieAlgebra",
    "ChevalleyBasis",
    "HighestWeightModule",
    "WeylModule",
    "IrreducibleModules",
    "GModuleByMats",
    "Action",
    "ModuleOfExtension",
    "Basis"
] do
    if IsBoundGlobal(name41) then
        Print("  ", name41, " is available.\n");
    else
        Print("  ", name41, " is NOT available.\n");
    fi;
od;

LF4_41 := SimpleLieAlgebra("F", 4, F7_41);;

Print("\nConstructed LF4_41 = SimpleLieAlgebra(\"F\",4,GF(7)).\n");
Print("Dimension(LF4_41) = ", Dimension(LF4_41), "\n");
Print("This should be the 52-dimensional adjoint Lie algebra, not V26.\n");

fundamentalWeights41 := [
    [1,0,0,0],
    [0,1,0,0],
    [0,0,1,0],
    [0,0,0,1]
];;

mods41 := [];;

DO_DIRECT_26_TRIAL_41 := true;;

if DO_DIRECT_26_TRIAL_41 and IsBoundGlobal("HighestWeightModule") then

    HWM41 := ValueGlobal("HighestWeightModule");;

    Print("\nTrying HighestWeightModule on the four fundamental weights:\n");

    for wt41 in fundamentalWeights41 do
        Vtmp41 := HWM41(LF4_41, wt41);;
        dtmp41 := Dimension(Vtmp41);;

        Print("  weight ", wt41, " gives dimension ", dtmp41, "\n");

        Add(mods41, rec(weight := wt41,
                        module := Vtmp41,
                        dimension := dtmp41));
    od;

    good26mods41 := Filtered(mods41, r -> r.dimension = 26);;

    if Length(good26mods41) = 0 then
        Print("\nNo 26-dimensional module found from these four weights.\n");
        Print("This may mean the constructor has a different convention,\n");
        Print("or the minimal module must be built another way.\n");
    else
        V26_41 := good26mods41[1].module;;
        weight26_41 := good26mods41[1].weight;;

        Print("\nFOUND 26-dimensional F4 module.\n");
        Print("Stored as V26_41.\n");
        Print("Highest weight used = ", weight26_41, "\n");
        Print("Dimension(V26_41) = ", Dimension(V26_41), "\n");
    fi;

else
    Print("\nHighestWeightModule is not available, or direct trial is switched off.\n");
    Print("We need another construction route for the 26-dimensional module.\n");
fi;


############################################################
# PART 5. Function-name probe for the next step
#
# This helps us see what OSCAR/GAP functions are available
# for constructing modules, actions, matrices, or bases.
############################################################

Print("\n------------------------------------------------------------\n");
Print("PART 5: FUNCTION-NAME PROBE FOR NEXT STEP\n");
Print("------------------------------------------------------------\n");

ShowNamesContaining41 := function(s)
    local hits, maxshow;

    hits := Filtered(NamesGVars(),
        n -> PositionSublist(LowercaseString(n), LowercaseString(s)) <> fail);

    maxshow := Minimum(Length(hits), 80);

    Print("\nNames containing \"", s, "\". Showing ",
          maxshow, " of ", Length(hits), ":\n");

    if maxshow > 0 then
        Print(hits{[1..maxshow]}, "\n");
    fi;
end;;

ShowNamesContaining41("module");
ShowNamesContaining41("highest");
ShowNamesContaining41("weight");
ShowNamesContaining41("action");
ShowNamesContaining41("matrix");
ShowNamesContaining41("basis");
ShowNamesContaining41("representation");


############################################################
# PART 6. Final report
############################################################

Print("\n============================================================\n");
Print("STEP 41A FINISHED\n");
Print("============================================================\n");

Print("\nStored abstract PSL2(13) objects:\n");
Print("  H41\n");
Print("  g41, f41, t41\n");
Print("  P41, NP41, B41\n");

Print("\nStored 14-point reference objects:\n");
Print("  hom14_41\n");
Print("  g14perm_41, f14perm_41, t14perm_41\n");
Print("  B14perm_41, G14perm_41\n");

Print("\nStored 12-dimensional quotient objects:\n");
Print("  g12_41, f12_41, t12_41\n");
Print("  B12_41, G12_41\n");

Print("\nStored F4 objects:\n");
Print("  LF4_41\n");

if IsBound(V26_41) then
    Print("  V26_41 was found directly.\n");
    Print("  weight26_41 = ", weight26_41, "\n");
else
    Print("  V26_41 was not found directly in this run.\n");
    Print("  Next step: construct the 26-dimensional module by another route.\n");
fi;

Print("\nCurrent interpretation:\n");
Print("  This is a fresh start after exhausting the pure Weyl-lift t search.\n");
Print("  The 12-dimensional quotient module is now built explicitly.\n");
Print("  The next target is to find or construct the missing 14-dimensional piece,\n");
Print("  then compare the 12 plus 14 action with the expected 26-dimensional\n");
Print("  minimal F4 module route suggested in the meeting.\n");

Print("\n============================================================\n");

LogTo();
