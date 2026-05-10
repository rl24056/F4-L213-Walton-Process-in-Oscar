############################################################
# PSL2_13_external_Bruhat_t_steps27_28.g
#
# One-piece GitHub / copy-paste GAP script.
#
# Purpose:
#   Continue after the hybrid F4(7) torus-normaliser obstruction.
#
#   The hybrid model found only the internal normalising involution
#   f^3 inside B = <g,f> = 13:6.  This GAP script returns to the
#   abstract group PSL2(13), constructs the genuine external Bruhat
#   involutions t, and analyses their action on:
#
#       f
#       <f>
#       f^3
#       B = <g,f>
#
#   Step 27:
#       Analyse all genuine external Bruhat t's.
#
#   Step 28:
#       Isolate the exact-inverting external Bruhat t's satisfying
#       f^t = f^-1, which is the Walton-style extended-normaliser
#       condition.
#
# How to run:
#
#       gap -q PSL2_13_external_Bruhat_t_steps27_28.g
#
# This file is self-contained.  It rebuilds the Step-26 objects:
#
#       H = PSL(2,13)
#       g of order 13
#       f of order 6 with action exponent 10 on <g>
#       B = <g,f>
#       GoodTs = genuine external Bruhat t elements with witnesses b
############################################################

Print("\n============================================================\n");
Print("PSL2(13) EXTERNAL BRUHAT t ANALYSIS: STEPS 27--28\n");
Print("============================================================\n");

############################################################
# SETUP FROM STEP 26
############################################################

Print("\n============================================================\n");
Print("SETUP: REBUILD ABSTRACT PSL2(13) WALTON DATA\n");
Print("============================================================\n");

H := PSL(2,13);;
Print("Order(H) = ", Size(H), "\n");

elts := Elements(H);;

g_candidates := Filtered(elts, x -> Order(x) = 13);;
Print("Number of elements of order 13 = ", Length(g_candidates), "\n");

if Length(g_candidates) = 0 then
    Error("No element of order 13 found in PSL(2,13).");
fi;

g := g_candidates[1];;
P := Group(g);;

Print("Order(g) = ", Order(g), "\n");
Print("Order(<g>) = ", Size(P), "\n");

NH_P := Normalizer(H,P);;
Print("Order(N_H(<g>)) = ", Size(NH_P), "\n");
Print("StructureDescription(N_H(<g>)) = ", StructureDescription(NH_P), "\n");

############################################################
# BASIC HELPERS
############################################################

ActionExponentOnG := function(x,g)
    local y,k;

    y := g^x;

    for k in [1..12] do
        if y = g^k then
            return k;
        fi;
    od;

    return fail;
end;;

ExprInGF := function(x)
    local i,j;

    for i in [0..12] do
        for j in [0..5] do
            if x = g^i * f^j then
                return [i,j];
            fi;
        od;
    od;

    return fail;
end;;

NormalisesSubgroup := function(x, K)
    return K^x = K;
end;;

FirstBruhatWitness := function(tt)
    local b0,e;

    for b0 in Elements(B) do
        if Order(b0*tt) = 3 then
            e := ExprInGF(b0);
            return [b0,e];
        fi;
    od;

    return fail;
end;;

ProductOrderDistribution := function(tt)
    local dist,b0,o;

    dist := [];

    for b0 in Elements(B) do
        o := Order(b0*tt);

        if not IsBound(dist[o]) then
            dist[o] := 0;
        fi;

        dist[o] := dist[o] + 1;
    od;

    return dist;
end;;

PrintDistribution := function(dist)
    local i;

    for i in [1..Length(dist)] do
        if IsBound(dist[i]) then
            Print("    Order ", i, " : ", dist[i], "\n");
        fi;
    od;
end;;

############################################################
# FIND f OF ORDER 6 IN N_H(<g>) ACTING BY EXPONENT 10
############################################################

f_candidates := [];;

for x in Elements(NH_P) do
    if Order(x) = 6 then
        if ActionExponentOnG(x,g) = 10 then
            Add(f_candidates,x);
        fi;
    fi;
od;

Print("Number of order-6 f candidates with action exponent 10 = ",
      Length(f_candidates), "\n");

if Length(f_candidates) = 0 then
    Error("No f found with action exponent 10.");
fi;

f := f_candidates[1];;
B := Group(g,f);;

Print("Order(f) = ", Order(f), "\n");
Print("Action exponent of f on <g> = ", ActionExponentOnG(f,g), "\n");
Print("Order(B=<g,f>) = ", Size(B), "\n");
Print("StructureDescription(B) = ", StructureDescription(B), "\n");

t_internal := f^3;;

Print("\nInternal involution f^3 check:\n");
Print("  Order(f^3) = ", Order(t_internal), "\n");
Print("  f^3 in B? ", t_internal in B, "\n");
Print("  f^3 normalises <g>? ", t_internal in Normalizer(H,P), "\n");
Print("  Action exponent of f^3 on <g> = ",
      ActionExponentOnG(t_internal,g), "\n");
Print("  Order(<g,f,f^3>) = ", Size(Group(g,f,t_internal)), "\n");

############################################################
# FIND GENUINE EXTERNAL BRUHAT INVOLUTIONS
############################################################

Print("\n------------------------------------------------------------\n");
Print("Searching for genuine external Bruhat involutions\n");

all_involutions := Filtered(elts, x -> Order(x) = 2);;
Print("Number of involutions in H = ", Length(all_involutions), "\n");

GoodTs := [];;

for ttest in all_involutions do

    # The genuine Bruhat t should not lie in B.
    if ttest in B then
        continue;
    fi;

    # It should not normalise <g>.
    if ttest in Normalizer(H,P) then
        continue;
    fi;

    # It should close <g,f> to H.
    if Size(Group(g,f,ttest)) <> Size(H) then
        continue;
    fi;

    # It should satisfy the order-3 Bruhat relation for some b in B.
    for btest in Elements(B) do
        if Order(btest*ttest) = 3 then
            Add(GoodTs, [ttest,btest]);
            break;
        fi;
    od;
od;

Print("Number of genuine external Bruhat t records found = ",
      Length(GoodTs), "\n");

if Length(GoodTs) = 0 then
    Error("No genuine external Bruhat t found. Something is wrong.");
fi;

GoodTSet := Set(List(GoodTs, pair -> pair[1]));;

Print("Number of distinct genuine external Bruhat t elements = ",
      Length(GoodTSet), "\n");

Print("\nSETUP COMPLETE.\n");

############################################################
# STEP 27:
# Analyse the genuine external Bruhat t in abstract PSL2(13)
#
# Purpose:
#   We now know the real Bruhat t is external:
#       t not in B
#       t not in N_H(<g>)
#       <g,f,t> = PSL2(13)
#
# Now we analyse what this t actually does to:
#       f
#       <f>
#       f^3
#       B = <g,f>
#
# This tells us which conditions are safe to impose later
# in the genuine F4(7) search.
############################################################

Print("\n============================================================\n");
Print("STEP 27: ACTION OF THE EXTERNAL BRUHAT t\n");
Print("============================================================\n");

############################################################
# Use first external Bruhat t
############################################################

t := GoodTs[1][1];;
b := GoodTs[1][2];;

Print("Order(t) = ", Order(t), "\n");
Print("t in B? ", t in B, "\n");
Print("t normalises <g>? ", t in Normalizer(H,P), "\n");
Print("Order(<g,f,t>) = ", Size(Group(g,f,t)), "\n");

Print("\nBruhat witness b:\n");
Print("Order(b*t) = ", Order(b*t), "\n");
Print("Expression of b in <g,f> = ", ExprInGF(b), "\n");

############################################################
# Does t invert f?
############################################################

Print("\n------------------------------------------------------------\n");
Print("Does external t invert f?\n");

Print("Order(f) = ", Order(f), "\n");
Print("Order(f^t) = ", Order(f^t), "\n");
Print("f^t = f^-1 ? ", f^t = f^-1, "\n");
Print("f^t is in <f>? ", f^t in Group(f), "\n");
Print("t normalises <f>? ", NormalisesSubgroup(t, Group(f)), "\n");

if f^t in B then
    Print("f^t lies in B, expression = ", ExprInGF(f^t), "\n");
else
    Print("f^t does not lie in B.\n");
fi;

############################################################
# What about the involution f^3?
############################################################

Print("\n------------------------------------------------------------\n");
Print("Action on the internal involution f^3\n");

t_internal := f^3;;

Print("Order(f^3) = ", Order(t_internal), "\n");
Print("(f^3)^t = f^3 ? ", t_internal^t = t_internal, "\n");
Print("(f^3)^t lies in B? ", t_internal^t in B, "\n");

if t_internal^t in B then
    Print("(f^3)^t expression in B = ", ExprInGF(t_internal^t), "\n");
fi;

############################################################
# Does t normalise B?
############################################################

Print("\n------------------------------------------------------------\n");
Print("Does external t normalise B=<g,f>?\n");

Print("t normalises B? ", NormalisesSubgroup(t, B), "\n");

if NormalisesSubgroup(t, B) then
    Print("Unexpected: t normalises B.\n");
else
    Print("Good: t does not normalise B, so it can enlarge B to PSL2(13).\n");
fi;

############################################################
# Product orders with powers of f
############################################################

Print("\n------------------------------------------------------------\n");
Print("Orders of f^j * t for j=0,...,5\n");

for j in [0..5] do
    Print("j=", j,
          " | Order(f^j*t) = ", Order(f^j*t), "\n");
od;

############################################################
# Product orders with all b in B
############################################################

Print("\n------------------------------------------------------------\n");
Print("Distribution of Order(b*t) for b in B\n");

prod_order_dist := [];;

for b0 in Elements(B) do
    o := Order(b0*t);

    if not IsBound(prod_order_dist[o]) then
        prod_order_dist[o] := 0;
    fi;

    prod_order_dist[o] := prod_order_dist[o] + 1;
od;

for i in [1..Length(prod_order_dist)] do
    if IsBound(prod_order_dist[i]) then
        Print("Order ", i, " : ", prod_order_dist[i], "\n");
    fi;
od;

############################################################
# Analyse all external Bruhat t elements
############################################################

Print("\n============================================================\n");
Print("ALL EXTERNAL BRUHAT t ELEMENTS\n");
Print("============================================================\n");

GoodTSet := Set(List(GoodTs, pair -> pair[1]));;

Print("Number of distinct external Bruhat t elements = ",
      Length(GoodTSet), "\n");

count_inverts_f := 0;;
count_normalises_f := 0;;
count_centralises_f3 := 0;;
count_normalises_B := 0;;

for tt in GoodTSet do

    if f^tt = f^-1 then
        count_inverts_f := count_inverts_f + 1;
    fi;

    if NormalisesSubgroup(tt, Group(f)) then
        count_normalises_f := count_normalises_f + 1;
    fi;

    if (f^3)^tt = f^3 then
        count_centralises_f3 := count_centralises_f3 + 1;
    fi;

    if NormalisesSubgroup(tt, B) then
        count_normalises_B := count_normalises_B + 1;
    fi;

od;

Print("External t's inverting f = ", count_inverts_f, "\n");
Print("External t's normalising <f> = ", count_normalises_f, "\n");
Print("External t's centralising f^3 = ", count_centralises_f3, "\n");
Print("External t's normalising B = ", count_normalises_B, "\n");

############################################################
# For each external t, find one Bruhat witness b=g^i*f^j
############################################################

Print("\n------------------------------------------------------------\n");
Print("Bruhat witness expressions for all external t's\n");

for tt in GoodTSet do
    found := false;

    for b0 in Elements(B) do
        if Order(b0*tt) = 3 then
            e := ExprInGF(b0);

            if e <> fail then
                key := Concatenation("g^", String(e[1]), "*f^", String(e[2]));
                Print("t witness: b = ", key, "\n");
            fi;

            found := true;
            break;
        fi;
    od;

    if not found then
        Print("No witness found for one external t. This should not happen.\n");
    fi;
od;

Print("============================================================\n");
Print("STEP 27 FINAL CONCLUSION\n");
Print("============================================================\n");

Print("The real external Bruhat t is not the same as f^3.\n");
Print("It lies outside B and outside the normaliser of <g>.\n");
Print("The data above tells us whether exact inversion of f is valid\n");
Print("or too strict for the next F4(7) search.\n");

Print("============================================================\n");
Print("END STEP 27\n");
Print("============================================================\n");

############################################################
# STEP 28:
# Exact-inverting external Bruhat t's in abstract PSL2(13)
#
# Purpose:
#   Step 27 should show:
#       external Bruhat t elements in total,
#       but only some invert f.
#
# This is important because Walton's method searches inside an
# extended centraliser / normaliser of f, i.e. among elements
# satisfying t*f*t^-1 = f^-1.
#
# Now we isolate exactly those t's and record their fingerprint.
############################################################

Print("\n============================================================\n");
Print("STEP 28: EXACT-INVERTING EXTERNAL BRUHAT t FINGERPRINT\n");
Print("============================================================\n");

############################################################
# Basic centraliser and normaliser of f
############################################################

Cf := Centralizer(H,f);;
Nf := Normalizer(H,Group(f));;

Print("Order(C_H(f)) = ", Size(Cf), "\n");
Print("StructureDescription(C_H(f)) = ", StructureDescription(Cf), "\n");

Print("Order(N_H(<f>)) = ", Size(Nf), "\n");
Print("StructureDescription(N_H(<f>)) = ", StructureDescription(Nf), "\n");

Print("Order(<f>) = ", Size(Group(f)), "\n");

############################################################
# Collect exact-inverting external t's
############################################################

GoodTSet := Set(List(GoodTs, pair -> pair[1]));;

ExactInvertingExternalTs := Filtered(
    GoodTSet,
    tt -> Order(tt) = 2
          and f^tt = f^-1
          and not (tt in B)
          and not (tt in Normalizer(H,P))
          and Size(Group(g,f,tt)) = Size(H)
);;

Print("\nNumber of external Bruhat t's = ", Length(GoodTSet), "\n");
Print("Number of exact-inverting external t's = ",
      Length(ExactInvertingExternalTs), "\n");

############################################################
# Compare with the inverting coset in N_H(<f>)
############################################################

AllInvertersOfF := Filtered(
    Elements(H),
    x -> Order(x) = 2 and f^x = f^-1
);;

Print("Number of involutions in H inverting f = ",
      Length(AllInvertersOfF), "\n");

Print("All exact inverters lie in N_H(<f>)? ",
      ForAll(AllInvertersOfF, x -> x in Nf), "\n");

Print("All exact inverters are outside C_H(f)? ",
      ForAll(AllInvertersOfF, x -> not (x in Cf)), "\n");

############################################################
# Analyse each exact-inverting external t
############################################################

Print("\n============================================================\n");
Print("INDIVIDUAL EXACT-INVERTING EXTERNAL t's\n");
Print("============================================================\n");

idx := 0;;

for tt in ExactInvertingExternalTs do
    idx := idx + 1;

    witness := FirstBruhatWitness(tt);
    dist := ProductOrderDistribution(tt);

    Print("\n------------------------------------------------------------\n");
    Print("Exact-inverting external t #", idx, "\n");

    Print("Order(t) = ", Order(tt), "\n");
    Print("t in B? ", tt in B, "\n");
    Print("t normalises <g>? ", tt in Normalizer(H,P), "\n");
    Print("t normalises <f>? ", NormalisesSubgroup(tt,Group(f)), "\n");
    Print("f^t = f^-1? ", f^tt = f^-1, "\n");
    Print("(f^3)^t = f^3? ", (f^3)^tt = f^3, "\n");
    Print("t normalises B? ", NormalisesSubgroup(tt,B), "\n");
    Print("Order(<g,f,t>) = ", Size(Group(g,f,tt)), "\n");

    if witness <> fail then
        Print("First Bruhat witness b expression = ", witness[2], "\n");
        Print("Order(b*t) = ", Order(witness[1]*tt), "\n");
    else
        Print("No Bruhat witness found. This should not happen.\n");
    fi;

    Bt := B^tt;;
    IntBBt := Intersection(B,Bt);;

    Print("Order(B intersection B^t) = ", Size(IntBBt), "\n");
    Print("StructureDescription(B intersection B^t) = ",
          StructureDescription(IntBBt), "\n");
    Print("B intersection B^t equals <f>? ",
          Size(IntBBt) = Size(Group(f)) and Group(f) = IntBBt, "\n");

    Print("Order(<g, g^t>) = ", Size(Group(g,g^tt)), "\n");

    Print("Distribution of Order(b*t), b in B:\n");
    PrintDistribution(dist);
od;

############################################################
# Count witness expressions among exact-inverting t's
############################################################

Print("\n============================================================\n");
Print("WITNESS EXPRESSIONS FOR EXACT-INVERTING t's\n");
Print("============================================================\n");

for tt in ExactInvertingExternalTs do
    witness := FirstBruhatWitness(tt);

    if witness <> fail then
        Print("witness b = g^", witness[2][1],
              " * f^", witness[2][2], "\n");
    fi;
od;

############################################################
# Final target conditions
############################################################

Print("\n============================================================\n");
Print("STEP 28 FINAL TARGET FINGERPRINT\n");
Print("============================================================\n");

Print("For the next genuine F4(7) search, a Walton-style exact-inverting t should satisfy:\n");
Print("  Order(t) = 2\n");
Print("  Trace(t on L(F4)) = -4\n");
Print("  t inverts f\n");
Print("  t centralises f^3\n");
Print("  t does not lie in B=<g,f>\n");
Print("  t does not normalise <g>\n");
Print("  t does not normalise B\n");
Print("  there exists b in B with Order(b*t)=3\n");
Print("  <g,f,t> has order 1092\n");

Print("\nIn abstract PSL2(13), the number of such exact-inverting external t's is ",
      Length(ExactInvertingExternalTs), ".\n");

Print("============================================================\n");
Print("END STEP 28\n");
Print("============================================================\n");

Print("\n============================================================\n");
Print("END PSL2(13) EXTERNAL BRUHAT t ANALYSIS: STEPS 27--28\n");
Print("============================================================\n");
