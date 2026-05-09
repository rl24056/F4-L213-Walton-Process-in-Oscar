############################################################
# F4(2) L2(13) Walton-style t-search
#
# File name suggestion:
# F4_2_L213_orbit_representative_t_search_failed.g
#
# Purpose:
# 1. Build G = F4(2).
# 2. Find g of order 13.
# 3. Find all f of order 6 such that <g,f> = 13:6.
# 4. Search exact inverting involutions t satisfying t f t^-1 = f^-1.
# 5. Test the Bruhat-style relation Order(b*t)=3 for b in <g,f>.
# 6. Classify exact inverting t's into local orbits.
# 7. Show that the Walton-style t-route does not give PSL(2,13).
# 8. Analyse the generated subgroup orders:
#       either PSL(4,3):C2 or the whole F4(2).
############################################################

LoadPackage("AtlasRep");;

############################################################
# Helper functions
############################################################

F4MultOrderMod13 := function(a)
    local x, n;

    if Gcd(a,13) <> 1 then
        return 0;
    fi;

    x := a mod 13;
    n := 1;

    while x <> 1 do
        x := (x*a) mod 13;
        n := n + 1;
    od;

    return n;
end;;

F4ActionExponent := function(x,g)
    local a;

    for a in [1..12] do
        if x*g*x^-1 = g^a then
            return a;
        fi;
    od;

    return 0;
end;;

F4InvertsF := function(t,f)
    return t*f*t^-1 = f^-1;
end;;

F4MovesGOutsideItsOwn13Subgroup := function(t,g)
    return not (t*g*t^-1 in Group(g));
end;;

F4BuildBWords := function(g,f)
    local words,k,j;

    words := [];

    for k in [0..12] do
        for j in [0..5] do
            Add(words,[g^k*f^j,k,j]);
        od;
    od;

    return words;
end;;

F4FindBruhatRelation := function(BWords,t)
    local item,b,k,j;

    for item in BWords do
        b := item[1];
        k := item[2];
        j := item[3];

        if Order(b*t) = 3 then
            return [true,k,j,b];
        fi;
    od;

    return [false,-1,-1,fail];
end;;

F4BTOrderProfileOneT := function(g,f,t)
    local orders,k,j,b;

    orders := [];

    for k in [0..12] do
        for j in [0..5] do
            b := (g^k)*(f^j);
            AddSet(orders,Order(b*t));
        od;
    od;

    return orders;
end;;

############################################################
# Step 1: Build F4(2), choose g, and find good f-elements
############################################################

Print("======================================================\n");
Print("STEP 1: SETUP F4(2), g, AND GOOD f-ELEMENTS\n");
Print("======================================================\n");

G := AtlasGroup("F4(2)");;

Print("Order of G = ", Size(G), "\n");

S := SylowSubgroup(G,13);;
g := GeneratorsOfGroup(S)[1];;

if Order(g) <> 13 then
    repeat
        g := Random(S);
    until Order(g) = 13;
fi;

Cg := Centralizer(G,g);;
NgS := Normalizer(G,S);;

Print("Order of S = ", Size(S), "\n");
Print("Order of g = ", Order(g), "\n");
Print("Order of C_G(g) = ", Size(Cg), "\n");
Print("Order of N_G(<g>) = ", Size(NgS), "\n");

GoodFs := [];;
ActionExponents := [];;

for x in Elements(NgS) do

    if Order(x) = 6 then

        a := F4ActionExponent(x,g);

        if a <> 0 and F4MultOrderMod13(a) = 6 and Size(Group(g,x)) = 78 then
            Add(GoodFs,x);
            AddSet(ActionExponents,a);
        fi;

    fi;

od;

DistinctFSubgroups := [];;

for f in GoodFs do
    if not (Group(f) in DistinctFSubgroups) then
        Add(DistinctFSubgroups,Group(f));
    fi;
od;

Print("Number of suitable order-6 f-elements = ", Length(GoodFs), "\n");
Print("Number of distinct cyclic subgroups <f> = ", Length(DistinctFSubgroups), "\n");
Print("Action exponents found = ", ActionExponents, "\n");

for a in ActionExponents do
    Print("Exponent ", a, " has multiplicative order ", F4MultOrderMod13(a), " modulo 13\n");
od;

############################################################
# Step 2: Exact t-search inside N_G(<f>)
############################################################

Print("======================================================\n");
Print("STEP 2: EXACT WALTON-STYLE SEARCH INSIDE N_G(<f>)\n");
Print("======================================================\n");

Hstd := PSL(2,13);;
PSLOrder := Size(Hstd);;

ExactResults := [];;
TotalBroad := 0;;
TotalBruhat := 0;;
TotalPSL := 0;;

Print("Order of PSL(2,13) = ", PSLOrder, "\n");

for fnum in [1..Length(GoodFs)] do

    f := GoodFs[fnum];;
    B := Group(g,f);;
    F := Group(f);;
    Nf := Normalizer(G,F);;
    BWords := F4BuildBWords(g,f);;

    BroadCount := 0;;
    BruhatCount := 0;;
    PSLCount := 0;;

    Print("------------------------------------------------------\n");
    Print("f number = ", fnum, "\n");
    Print("Order of f = ", Order(f), "\n");
    Print("Action exponent of f on <g> = ", F4ActionExponent(f,g), "\n");
    Print("Order of <g,f> = ", Size(B), "\n");
    Print("Order of N_G(<f>) = ", Size(Nf), "\n");

    for t in Elements(Nf) do

        if Order(t) = 2 and F4InvertsF(t,f) and F4MovesGOutsideItsOwn13Subgroup(t,g) then

            BroadCount := BroadCount + 1;;
            bruhat := F4FindBruhatRelation(BWords,t);;

            if bruhat[1] = true then

                BruhatCount := BruhatCount + 1;;
                Hgen := Group(g,f,t);;
                hsize := Size(Hgen);;

                Print("Bruhat candidate found\n");
                Print("k = ", bruhat[2], ", j = ", bruhat[3], "\n");
                Print("Order of (g^k f^j)t = ", Order(bruhat[4]*t), "\n");
                Print("Order of <g,f,t> = ", hsize, "\n");

                if hsize = PSLOrder then
                    PSLCount := PSLCount + 1;;
                fi;

            fi;

        fi;

    od;

    TotalBroad := TotalBroad + BroadCount;;
    TotalBruhat := TotalBruhat + BruhatCount;;
    TotalPSL := TotalPSL + PSLCount;;

    Print("Broad t candidates = ", BroadCount, "\n");
    Print("Bruhat candidates = ", BruhatCount, "\n");
    Print("PSL(2,13)-order triples = ", PSLCount, "\n");

    Add(ExactResults,[fnum,BroadCount,BruhatCount,PSLCount]);

od;

Print("======================================================\n");
Print("STEP 2 SUMMARY\n");
Print("======================================================\n");
Print("Exact results [fnum,broad_t,bruhat,psl] =\n");
Print(ExactResults, "\n");
Print("Total broad t candidates = ", TotalBroad, "\n");
Print("Total Bruhat candidates = ", TotalBruhat, "\n");
Print("Total PSL(2,13)-order triples = ", TotalPSL, "\n");

############################################################
# Step 3: Sanity check inside abstract PSL(2,13)
############################################################

Print("======================================================\n");
Print("STEP 3: SANITY CHECK INSIDE PSL(2,13)\n");
Print("======================================================\n");

H0 := PSL(2,13);;
S0 := SylowSubgroup(H0,13);;
g0 := GeneratorsOfGroup(S0)[1];;

if Order(g0) <> 13 then
    repeat
        g0 := Random(S0);
    until Order(g0) = 13;
fi;

N0 := Normalizer(H0,S0);;
GoodFs0 := [];;

for x in Elements(N0) do

    if Order(x) = 6 then

        a := F4ActionExponent(x,g0);

        if a <> 0 and F4MultOrderMod13(a) = 6 and Size(Group(g0,x)) = 78 then
            Add(GoodFs0,x);
        fi;

    fi;

od;

Print("Order of H0 = ", Size(H0), "\n");
Print("Order of S0 = ", Size(S0), "\n");
Print("Order of N_H0(S0) = ", Size(N0), "\n");
Print("Number of suitable f-elements in PSL(2,13) = ", Length(GoodFs0), "\n");

SanityGoodTriples := [];;
SanityBroadCount := 0;;
SanityBruhatCount := 0;;

for fnum in [1..Length(GoodFs0)] do

    f0 := GoodFs0[fnum];;
    F0 := Group(f0);;
    Nf0 := Normalizer(H0,F0);;
    BWords0 := F4BuildBWords(g0,f0);;

    for t0 in Elements(Nf0) do

        if Order(t0) = 2 and F4InvertsF(t0,f0) and F4MovesGOutsideItsOwn13Subgroup(t0,g0) then

            SanityBroadCount := SanityBroadCount + 1;;
            bruhat0 := F4FindBruhatRelation(BWords0,t0);;

            if bruhat0[1] = true then

                SanityBruhatCount := SanityBruhatCount + 1;;
                Hgen0 := Group(g0,f0,t0);;

                Print("Sanity Bruhat candidate found\n");
                Print("f0 number = ", fnum, "\n");
                Print("Action exponent of f0 = ", F4ActionExponent(f0,g0), "\n");
                Print("k = ", bruhat0[2], ", j = ", bruhat0[3], "\n");
                Print("Order of b*t0 = ", Order(bruhat0[4]*t0), "\n");
                Print("Order of <g0,f0,t0> = ", Size(Hgen0), "\n");

                if Size(Hgen0) = Size(H0) then
                    Add(SanityGoodTriples,[fnum,bruhat0[2],bruhat0[3],f0,t0,Hgen0]);
                    Print("SUCCESS: sanity check found PSL(2,13).\n");
                    break;
                fi;

            fi;

        fi;

    od;

    if Length(SanityGoodTriples) > 0 then
        break;
    fi;

od;

Print("======================================================\n");
Print("STEP 3 SUMMARY\n");
Print("======================================================\n");
Print("Sanity broad t count = ", SanityBroadCount, "\n");
Print("Sanity Bruhat-style t count = ", SanityBruhatCount, "\n");
Print("Number of sanity triples giving PSL(2,13) = ", Length(SanityGoodTriples), "\n");

############################################################
# Step 4: All-f local orbit check
############################################################

Print("======================================================\n");
Print("STEP 4: ALL-f ORBIT CHECK FOR EXACT INVERTING INVOLUTIONS\n");
Print("======================================================\n");

AllFOrbitData := [];;

for fnum in [1..Length(GoodFs)] do

    f := GoodFs[fnum];;
    B := Group(g,f);;
    z := f^3;;
    Cz := Centralizer(G,z);;
    Cf := Centralizer(G,f);;
    F := Group(f);;
    NCzF := Normalizer(Cz,F);;
    BWords := F4BuildBWords(g,f);;

    InvertingTs := [];;

    for t in Elements(NCzF) do
        if Order(t) = 2 and F4InvertsF(t,f) then
            Add(InvertingTs,t);
        fi;
    od;

    BruhatCount := 0;;

    for t in InvertingTs do
        bruhat := F4FindBruhatRelation(BWords,t);
        if bruhat[1] = true then
            BruhatCount := BruhatCount + 1;
        fi;
    od;

    OrbitsCf := Orbits(Cf,InvertingTs,OnPoints);;
    OrbitsNCzF := Orbits(NCzF,InvertingTs,OnPoints);;

    CfOrbitLengths := List(OrbitsCf,Length);;
    NCzFOrbitLengths := List(OrbitsNCzF,Length);;

    RepOrderProfiles := [];;
    GeneratedOrders := [];;

    for i in [1..Length(OrbitsNCzF)] do
        rep := OrbitsNCzF[i][1];;
        Add(RepOrderProfiles,F4BTOrderProfileOneT(g,f,rep));
        Add(GeneratedOrders,Size(Group(g,f,rep)));
    od;

    Add(AllFOrbitData,
        [fnum,
         F4ActionExponent(f,g),
         Size(Cf),
         Size(Cz),
         Size(NCzF),
         Length(InvertingTs),
         BruhatCount,
         CfOrbitLengths,
         NCzFOrbitLengths,
         RepOrderProfiles,
         GeneratedOrders]);

    Print("------------------------------------------------------\n");
    Print("f number = ", fnum, "\n");
    Print("action exponent = ", F4ActionExponent(f,g), "\n");
    Print("|C_G(f)| = ", Size(Cf), "\n");
    Print("|C_G(f^3)| = ", Size(Cz), "\n");
    Print("|N_{C_G(f^3)}(<f>)| = ", Size(NCzF), "\n");
    Print("number of exact inverting involutions = ", Length(InvertingTs), "\n");
    Print("Bruhat order-3 count = ", BruhatCount, "\n");
    Print("C_G(f)-orbit lengths = ", CfOrbitLengths, "\n");
    Print("N_{C_G(f^3)}(<f>)-orbit lengths = ", NCzFOrbitLengths, "\n");
    Print("order profiles for orbit reps = ", RepOrderProfiles, "\n");
    Print("generated orders for orbit reps = ", GeneratedOrders, "\n");

od;

Print("======================================================\n");
Print("STEP 4 SUMMARY\n");
Print("======================================================\n");
Print("Data format:\n");
Print("[fnum, action exponent, |C_G(f)|, |C_G(f^3)|, |N_C(<f>)|, number of inverting t, Bruhat count, C_G(f)-orbit lengths, N_C-orbit lengths, order profiles, generated orders]\n");
Print(AllFOrbitData, "\n");

############################################################
# Step 5: Separate small subgroup and whole-group outcomes
############################################################

Print("======================================================\n");
Print("STEP 5: SEPARATE GENERATED SUBGROUP TYPES\n");
Print("======================================================\n");

SmallOrderFs := [];;
WholeOrderFs := [];;

for row in AllFOrbitData do

    fnum := row[1];;
    genOrders := row[11];;

    if genOrders[1] = 12130560 then
        Add(SmallOrderFs,fnum);
    fi;

    if genOrders[1] = Size(G) then
        Add(WholeOrderFs,fnum);
    fi;

od;

Print("f-elements giving subgroup order 12130560:\n");
Print(SmallOrderFs, "\n");

Print("f-elements giving whole F4(2):\n");
Print(WholeOrderFs, "\n");

############################################################
# Step 6: Analyse representative small subgroup
############################################################

Print("======================================================\n");
Print("STEP 6: ANALYSE REPRESENTATIVE SMALL SUBGROUP\n");
Print("======================================================\n");

if Length(SmallOrderFs) > 0 then

    fnumSmall := SmallOrderFs[1];;
    fSmall := GoodFs[fnumSmall];;
    zSmall := fSmall^3;;
    CzSmall := Centralizer(G,zSmall);;
    FSmall := Group(fSmall);;
    NCzFSmall := Normalizer(CzSmall,FSmall);;

    InvertingTsSmall := [];;

    for t in Elements(NCzFSmall) do
        if Order(t) = 2 and F4InvertsF(t,fSmall) then
            Add(InvertingTsSmall,t);
        fi;
    od;

    tSmall := InvertingTsSmall[1];;
    HSmall := Group(g,fSmall,tSmall);;

    Print("Chosen f number = ", fnumSmall, "\n");
    Print("Order of HSmall = ", Size(HSmall), "\n");
    Print("Index of HSmall in G = ", Size(G)/Size(HSmall), "\n");

    Print("Is HSmall perfect? ", IsPerfect(HSmall), "\n");
    Print("Is HSmall simple? ", IsSimpleGroup(HSmall), "\n");

    Print("Centre size of HSmall = ", Size(Center(HSmall)), "\n");
    Print("Derived subgroup order = ", Size(DerivedSubgroup(HSmall)), "\n");

    Print("StructureDescription(HSmall), if GAP can identify it:\n");
    Print(StructureDescription(HSmall), "\n");

    NGHSmall := Normalizer(G,HSmall);;
    CGHSmall := Centralizer(G,HSmall);;

    Print("Order of N_G(HSmall) = ", Size(NGHSmall), "\n");
    Print("Order of C_G(HSmall) = ", Size(CGHSmall), "\n");
    Print("Index [N_G(HSmall):HSmall] = ", Size(NGHSmall)/Size(HSmall), "\n");

    SmallSubgroups := [];;

    for fnum in SmallOrderFs do

        f := GoodFs[fnum];;
        z := f^3;;
        Cz := Centralizer(G,z);;
        F := Group(f);;
        NCzF := Normalizer(Cz,F);;

        InvertingTs := [];;

        for t in Elements(NCzF) do
            if Order(t) = 2 and F4InvertsF(t,f) then
                Add(InvertingTs,t);
            fi;
        od;

        H := Group(g,f,InvertingTs[1]);;
        Add(SmallSubgroups,[fnum,H]);

    od;

    ConjToFirstSmall := [];;

    for item in SmallSubgroups do

        fnum := item[1];;
        H := item[2];;

        Add(ConjToFirstSmall,[fnum,IsConjugate(G,HSmall,H)]);

    od;

    Print("Conjugacy to first small subgroup [fnum, true/false]:\n");
    Print(ConjToFirstSmall, "\n");

else

    Print("No small subgroup cases found.\n");

fi;

############################################################
# Final summary
############################################################

Print("======================================================\n");
Print("FINAL SUMMARY\n");
Print("======================================================\n");

Print("Order of G = ", Size(G), "\n");
Print("Number of suitable f-elements = ", Length(GoodFs), "\n");
Print("Action exponents = ", ActionExponents, "\n");

Print("Exact search inside N_G(<f>):\n");
Print("Total broad t candidates = ", TotalBroad, "\n");
Print("Total Bruhat candidates = ", TotalBruhat, "\n");
Print("Total PSL(2,13)-order triples = ", TotalPSL, "\n");

Print("Sanity check inside PSL(2,13):\n");
Print("Number of sanity triples giving PSL(2,13) = ", Length(SanityGoodTriples), "\n");

Print("All-f orbit check:\n");
Print("Small-order f-elements = ", SmallOrderFs, "\n");
Print("Whole-group f-elements = ", WholeOrderFs, "\n");

if Length(SmallOrderFs) > 0 then
    Print("Representative small subgroup order = ", Size(HSmall), "\n");
    Print("Representative small subgroup index in G = ", Size(G)/Size(HSmall), "\n");
    Print("StructureDescription = ", StructureDescription(HSmall), "\n");
    Print("Normalizer order = ", Size(NGHSmall), "\n");
    Print("Centralizer order = ", Size(CGHSmall), "\n");
    Print("Conjugacy data for small cases = ", ConjToFirstSmall, "\n");
fi;

Print("Conclusion:\n");
Print("The local 13:6 construction works, and the abstract PSL(2,13) sanity check works.\n");
Print("However, in F4(2), the exact inverting involutions form single local orbits and never satisfy the Bruhat order-3 relation.\n");
Print("Adding an exact inverting t gives either PSL(4,3):C2 or the whole F4(2), not PSL(2,13).\n");
Print("Thus the Walton-style orbit-representative t-test fails for this F4(2) model.\n");

Print("======================================================\n");
Print("END OF SCRIPT\n");
Print("======================================================\n");
