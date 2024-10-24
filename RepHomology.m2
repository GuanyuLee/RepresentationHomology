-*
   Copyright 2024, .
*-

newPackage(
    "RepHomology",
    Version => "0.95",
    Date => "October, 2024",
    Authors => {
	{Name => "Guanyu Li", Email => "gl479@cornell.edu", HomePage => "https://sites.google.com/view/guanyu-li-math/home"}},
    Headline => "Representation Homology",
    Keywords => {"Derived algebraic geometry"},
    AuxiliaryFiles => false,
    PackageExports => {"Complexes"},
    DebuggingMode => false
    )

export { -- methods
    "surfaceRepHomologyGroup",
    "surfaceRepHomologyAlg",
    "surfaceRepHomologyLie",
    "link",
    "linkRepHomology",
    "word",
    "braidIndex",
    -- types
    "GroupType",
    "AlgType",
    "LieType",
    "Homogenize",
    "Link",
    "Trefoil",
    "FigureEight"
    }

-------------------
--The type Link
-------------------

Link = new Type of MutableHashTable
Link.synonym = "link"
  -- key:
  -- BraidIndex
  -- LinkWord
  -- cache: a CacheTable

Link.GlobalAssignHook = globalAssignFunction
Link.GlobalReleaseHook = globalReleaseFunction

-- Construct a link
link = method()
link (ZZ, List) := (n,w) -> (
	new Link from {
        protect symbol BraidIndex => n,
        protect symbol LinkWord => w,
        symbol cache => new CacheTable from {"name" => "Unnamed Link"}
	}
)

Trefoil = link (2,{1,1,1});
FigureEight = link (3,{1,-2,1,-2});

length (Link) := (l) -> ( # (l.LinkWord))

braidIndex = method()
braidIndex (Link) := (l) -> (l.BraidIndex)

word = method()
word (Link) := (l) -> (l.LinkWord)

isWellDefined (Link) := Boolean => (l) -> (
    for n in word(l) do (
        if (n == 0) then (return false);
        if (n > braidIndex(l)-1) or ((-n) > braidIndex(l)-1) then (return false);
    );
    true
)

----------------------------------------------------
--Representation homology of surfaces
----------------------------------------------------

-* 
Types:
CoefficientRing : coefficient ring of the group scheme
GroupType : type of the group scheme, a string, including "B", "Borel", "U", "Unipotent", "GL" and "SL"
Homogenize : boolean variable, indicator whether to have homogeneous coordinate ring for unipotent and Borel cases
Variables : a list of symbols of matrices

Inputs: 
n = matrixSize : size of matrices, or equivalently dimension of the group scheme
g = genus : genus of matrices, (half of) the number of matrices to be generated

Output: 2 lists of g many matrices, of size n*n, of the given group type

Private function
*-

makeMatricesGroup = method (Options => {
        CoefficientRing => QQ,
        GroupType => "GL",
        Homogenize => false,
        Variables => {getSymbol "x", getSymbol "y", getSymbol "s", getSymbol "t"}
        })
makeMatricesGroup(ZZ, ZZ) := (List, List) => opts -> (matrixSize, genusOfSurface) -> (
    -- setup
    variables := opts.Variables;
    n := matrixSize;
    g := genusOfSurface;
    local XX; local YY; local XDeg; local YDeg; local S; local T; local SDeg; local TDeg; local R; local X; local Y; local M; local N; local I; local Xnew; local Ynew;
    
    if opts.GroupType == "GL" then ( -- General linear groups
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_1)_(k,i,j);
        S = flatten for k from 1 to g list (variables_2)_(k);
        T = flatten for k from 1 to g list (variables_3)_(k);

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY, S, T)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_0)_(k,i+1,j+1))_R);
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_1)_(k,i+1,j+1))_R);

        M = for k from 0 to g-1 list ((variables_2)_(k+1))_R*det(X_k)-1;
        N = for k from 0 to g-1 list ((variables_3)_(k+1))_R*det(Y_k)-1;
        I = ideal join(M,N);
        Xnew = for x in X list sub(x,R/I);
        Ynew = for y in Y list sub(y,R/I);
    )
    else if opts.GroupType == "SL" then ( -- Special linear groups
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_1)_(k,i,j);

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_0)_(k,i+1,j+1))_R);
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_1)_(k,i+1,j+1))_R);

        M = for k from 0 to g-1 list det(X_k)-1;
        N = for k from 0 to g-1 list det(Y_k)-1;
        I = ideal join(M,N);
        Xnew = for x in X list sub(x,R/I);
        Ynew = for y in Y list sub(y,R/I);
    )
    else if (opts.GroupType == "U") or (opts.GroupType == "Unipotent") or (opts.GroupType == "AnUnipotent") then ( -- Unipotent groups
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_0)_(k,i,j);
        XDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list 1;
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_1)_(k,i,j);
        YDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list 1;

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY), Degrees => join(XDeg, YDeg)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<j then ((variables_0)_(k,i+1,j+1))_R else if i==j then 1 else 0));
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<j then ((variables_1)_(k,i+1,j+1))_R else if i==j then 1 else 0));
        
        Xnew = X;
        Ynew = Y;
    )
    else if (opts.GroupType == "B") or (opts.GroupType == "Borel") then ( -- Borel groups
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list (variables_1)_(k,i,j);
        S = flatten for k from 1 to g list (variables_2)_(k);
        T = flatten for k from 1 to g list (variables_3)_(k);

        XDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list 1;
        YDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list 1;
        SDeg = if opts.Homogenize then
            flatten for k from 1 to g list 0
            else flatten for k from 1 to g list 1;
        TDeg = if opts.Homogenize then
            flatten for k from 1 to g list 0
            else flatten for k from 1 to g list 1;

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY, S, T), Degrees => join(XDeg, YDeg, SDeg, TDeg)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<=j then ((variables_0)_(k,i+1,j+1))_R else 0));
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<=j then ((variables_1)_(k,i+1,j+1))_R else 0));

        M = for k from 0 to g-1 list ((variables_2)_(k+1))_R*det(X_k)-1;
        N = for k from 0 to g-1 list ((variables_3)_(k+1))_R*det(Y_k)-1;
        I = ideal join(M,N);
        
        Xnew = for x in X list sub(x,R/I);
        Ynew = for y in Y list sub(y,R/I);
    ) else error "The group type is not supported.";
    (Xnew, Ynew)
    )

surfaceRepHomologyChainGroup = method (Options => {
        GroupType => "GL"
        })
surfaceRepHomologyChainGroup(Matrix, ZZ, ZZ) := Complex => opts -> (M, matrixSize, genusOfSurface) -> (
    n := matrixSize;
    g := genusOfSurface;
    if opts.GroupType == "GL" then (
        return koszulComplex matrix {flatten for i from 0 to n-1 list
            for j from 0 to n-1 list if i==j then M_(i,j)-1 else M_(i,j)};
    )
    else if opts.GroupType == "SL" then(
        L := flatten for i from 0 to n-1 list
            for j from 0 to n-1 list if i==j then M_(i,j)-1 else M_(i,j);
        return koszulComplex matrix {drop(L, -1)};
    )
    else if (opts.GroupType == "U") or (opts.GroupType == "Unipotent") or (opts.GroupType == "AnUnipotent") then (
        return koszulComplex matrix {flatten for i from 0 to n-1 list
            for j from i+1 to n-1 list M_(i,j)};
    )
    else if (opts.GroupType == "B") or (opts.GroupType == "Borel") then (
        return koszulComplex matrix {flatten for i from 0 to n-1 list
            for j from i to n-1 list if i==j then M_(i,j)-1 else M_(i,j)};
    ) else error "The group type is not supported.";
)

-*
print the homology group of a Koszul complex

Warning : the function is valid for non-Koszul complexes, however it stops when the first time the homology is 0
*-
printKoszulHH = method ()
printKoszulHH(Complex) := C -> (
    local H; local D;
    H = for i from 0 to (length C) list (
        D = prune HH(i,C);
        if D == 0 then break;
        << "H_" << i << " = " << D << endl;
        D
        );
    H
    )

-* Inputs:
kk : ground ring
n : size of matrices
g : genus of the commuting variety
Group : type of the group scheme, a string, including "B", "Borel", "U", "Unipotent", "GL" and "SL"
*-
surfaceRepHomologyGroup = method (Options => options makeMatricesGroup)
surfaceRepHomologyGroup(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    -- construct the matrices
    (X, Y) := makeMatricesGroup(n, g, CoefficientRing => opts.CoefficientRing, GroupType => opts.GroupType, Variables => opts.Variables);

    -- the matrix for the complex
    M := product for k from 0 to g-1 list (X_k * Y_k * inverse(X_k) * inverse(Y_k));

    -- construct the koszul complex
    C := surfaceRepHomologyChainGroup(M, n, g, GroupType => opts.GroupType);

    -- print the result
    printKoszulHH(C)
)

----------------------------------------------------
--Algebra version of representation homology of surfaces
----------------------------------------------------

makeMatricesAlg = method (Options => {
        Homogenize => false,
        CoefficientRing => QQ,
        AlgType => "gl",
        Variables => {getSymbol "x", getSymbol "y"}
        })
makeMatricesAlg(ZZ, ZZ) := (List, List) => opts -> (matrixSize, genus) -> (
    n := matrixSize;
    g := genus;
    variables := opts.Variables;
    local XX; local YY; local XDeg; local YDeg; local S; local T; local SDeg; local TDeg; local R; local X; local Y; local M; local N; local I; local Xnew; local Ynew;
    if opts.AlgType == "gl" then (
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_1)_(k,i,j);

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_0)_(k,i+1,j+1))_R);
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_1)_(k,i+1,j+1))_R);

        (Xnew, Ynew) = (X, Y);
    )
    else if opts.AlgType == "sl" then (
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from 1 to n list (variables_1)_(k,i,j);

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_0)_(k,i+1,j+1))_R);
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> ((variables_1)_(k,i+1,j+1))_R);

        M = for k from 0 to g-1 list trace(X_k);
        N = for k from 0 to g-1 list trace(Y_k);
        I = ideal join(M,N);

        Xnew = for x in X list sub(x,R/I);
        Ynew = for y in Y list sub(y,R/I);
    )
    else if (opts.AlgType == "n") or (opts.AlgType == "nilpotent") then (
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_0)_(k,i,j);
        XDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list 1;
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_1)_(k,i,j);
        YDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list 1;

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY), Degrees => join(XDeg, YDeg)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<j then ((variables_0)_(k,i+1,j+1))_R else 0));
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<j then ((variables_1)_(k,i+1,j+1))_R else 0));

        (Xnew, Ynew) = (X, Y);
    ) else if (opts.AlgType == "b") or (opts.AlgType == "borel") then (
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list (variables_0)_(k,i,j);
        XDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list 1;
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list (variables_1)_(k,i,j);
        YDeg = if opts.Homogenize then
            flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list j-i
            else flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i to n list 1;

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY), Degrees => join(XDeg, YDeg)];

        -- make matrices
        X = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<=j then ((variables_0)_(k,i+1,j+1))_R else 0));
        Y = for k from 1 to g list matrix table (n, n, (i,j) -> (if i<=j then ((variables_1)_(k,i+1,j+1))_R else 0));

        (Xnew, Ynew) = (X, Y);
    ) else error "The algebra type is not supported.";
    (Xnew, Ynew)
)

surfaceRepHomologyChainAlg = method (Options => {
        AlgType => "gl"
        })
surfaceRepHomologyChainAlg(Matrix, ZZ, ZZ) := Complex => opts -> (M, matrixSize, genusOfSurface) -> (
    n := matrixSize;
    g := genusOfSurface;
    if opts.AlgType == "gl" then (
        return koszulComplex matrix {flatten for i from 0 to n-1 list
            for j from 0 to n-1 list M_(i,j)};
    )
    else if (opts.AlgType == "n") or (opts.AlgType == "nilpotent") then (
        return koszulComplex matrix {flatten for i from 0 to n-1 list
            for j from i+1 to n-1 list M_(i,j)};
    )
    else if (opts.AlgType == "sl") then (
        L := flatten for i from 0 to n-1 list
            for j from 0 to n-1 list M_(i,j);
        return koszulComplex matrix {drop(L, 1)};
    )
    else if (opts.AlgType == "b") or (opts.AlgType == "borel") then (
        return koszulComplex matrix {flatten for i from 0 to n-1 list
            for j from i to n-1 list M_(i,j)};
    ) else error "The algebra type is not supported.";
)

surfaceRepHomologyAlg = method (Options => options makeMatricesAlg)
surfaceRepHomologyAlg(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    -- construct the matrices
    (X, Y) := makeMatricesAlg(n, g, CoefficientRing => opts.CoefficientRing, AlgType => opts.AlgType, Variables => opts.Variables);

    -- the matrix for the complex
    M := sum for k from 0 to g-1 list (X_k * Y_k - Y_k * X_k);

    -- construct the koszul complex
    C := surfaceRepHomologyChainAlg(M, n, g, AlgType => opts.AlgType);

    -- print the result
    printKoszulHH(C)
)

----------------------------------------------------
--Lie algebra version of representation homology of surfaces
----------------------------------------------------

elementaryMatrix = method ();
elementaryMatrix(ZZ, ZZ, ZZ) := (size, row, col) -> (
    matrix table (size, size, (i,j) -> (if (i+1 == row) and (j+1 == col) then 1 else 0))
)
elementaryMatrix(Ring, ZZ, ZZ, ZZ) := (R, size, row, col) -> (
    matrix table (size, size, (i,j) -> (if (i+1 == row) and (j+1 == col) then 1_R else 0_R))
)
elementaryMatrix(RingElement, ZZ, ZZ, ZZ) := (x, size, row, col) -> (
    x * elementaryMatrix(ring x, size, row, col)
)

makeMatricesLie = method (Options => {
        CoefficientRing => QQ,
        LieType => "DnNil",
        --Homogenize => false,
        Variables => {getSymbol "x", getSymbol "y", getSymbol "s", getSymbol "t", getSymbol "u", getSymbol "v"}
        })
makeMatricesLie(ZZ, ZZ) := (List, List) => opts -> (typeSize, genusOfSurface) -> (
    -- setup
    variables := opts.Variables;
    n := typeSize;
    g := genusOfSurface;
    local XX; local YY; local XDeg; local YDeg; local S; local T; local SDeg; local TDeg; local R; local X; local Y; local Xtemp; local Ytemp;
    local UU; local VV; local TT; local SS;
    
    if opts.LieType == "DnNil" then ( -- Dn type nilpotent algebras
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_1)_(k,i,j);
        SS = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_2)_(k,i,j);
        TT = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_3)_(k,i,j);

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY, SS, TT)];

        -- make matrices
        X = for k from 1 to g list (
            Xtemp = matrix table (2*n, 2*n, (i,j)->0_R);
            for i from 1 to n do
                for j from i+1 to n do
                    Xtemp = Xtemp + elementaryMatrix((((variables_0)_(k,i,j))_R), 2*n, i, j) + elementaryMatrix(-(((variables_0)_(k,i,j))_R), 2*n, j+n, i+n) + elementaryMatrix((((variables_1)_(k,i,j))_R), 2*n, i, j+n) + elementaryMatrix(-(((variables_1)_(k,i,j))_R), 2*n, j, i+n);
            Xtemp
            );
        
        S = for k from 1 to g list (
            Xtemp = matrix table (2*n, 2*n, (i,j)->0_R);
            for i from 1 to n do
                for j from i+1 to n do
                    Xtemp = Xtemp + elementaryMatrix((((variables_2)_(k,i,j))_R), 2*n, i, j) + elementaryMatrix(-(((variables_2)_(k,i,j))_R), 2*n, j+n, i+n) + elementaryMatrix((((variables_3)_(k,i,j))_R), 2*n, i, j+n) + elementaryMatrix(-(((variables_3)_(k,i,j))_R), 2*n, j, i+n);
            Xtemp
            );
    ) else if opts.LieType == "BnNil" then ( -- Bn type nilpotent algebras
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_1)_(k,i,j);
        SS = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_2)_(k,i,j);
        TT = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_3)_(k,i,j);
        UU = flatten for k from 1 to g list
            flatten for i from 1 to n list (variables_4)_(k,i);
        VV = flatten for k from 1 to g list
            flatten for i from 1 to n list (variables_5)_(k,i);

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY, SS, TT, UU, VV)];

        -- make matrices
        X = for k from 1 to g list (
            Xtemp = matrix table (2*n+1, 2*n+1, (i,j)->0_R);
            for i from 1 to n do
                for j from i+1 to n do
                    Xtemp = Xtemp + elementaryMatrix((((variables_0)_(k,i,j))_R), 2*n+1, i, j) + elementaryMatrix(-(((variables_0)_(k,i,j))_R), 2*n+1, j+n, i+n) + elementaryMatrix((((variables_1)_(k,i,j))_R), 2*n+1, i, j+n) + elementaryMatrix(-(((variables_1)_(k,i,j))_R), 2*n+1, j, i+n);
            for i from 1 to n do
                Xtemp = Xtemp + elementaryMatrix((((variables_4)_(k,i))_R), 2*n+1, i, 2*n+1) + elementaryMatrix(-(((variables_4)_(k,i))_R), 2*n+1, 2*n+1, i+n);
            Xtemp
            );
        
        S = for k from 1 to g list (
            Xtemp = matrix table (2*n+1, 2*n+1, (i,j)->0_R);
            for i from 1 to n do
                for j from i+1 to n do
                    Xtemp = Xtemp + elementaryMatrix((((variables_2)_(k,i,j))_R), 2*n+1, i, j) + elementaryMatrix(-(((variables_2)_(k,i,j))_R), 2*n+1, j+n, i+n) + elementaryMatrix((((variables_3)_(k,i,j))_R), 2*n+1, i, j+n) + elementaryMatrix(-(((variables_3)_(k,i,j))_R), 2*n+1, j, i+n);
            for i from 1 to n do
                Xtemp = Xtemp + elementaryMatrix((((variables_5)_(k,i))_R), 2*n+1, i, 2*n+1) + elementaryMatrix(-(((variables_5)_(k,i))_R), 2*n+1, 2*n+1, i+n);
            Xtemp
            );
    ) else if opts.LieType == "G2Nil" then (
        XX = flatten for k from 1 to 2*g list flatten {(variables_0)_(k),(variables_1)_(k),(variables_2)_(k),(variables_3)_(k),(variables_4)_(k),(variables_5)_(k)};
        
        R = opts.CoefficientRing[XX];

        X = for k from 1 to g list (matrix {{0,0,0,-2*((variables_3)_(k))_R,-2*((variables_2)_(k))_R,-2*((variables_0)_(k))_R,0},{((variables_2)_(k))_R,0,((variables_1)_(k))_R,((variables_5)_(k))_R,0,-((variables_3)_(k))_R,0},{((variables_0)_(k))_R,0,0,((variables_4)_(k))_R,((variables_3)_(k))_R,0,0},{0,0,0,0,0,0,0},{0,0,0,((variables_0)_(k))_R,0,0,0},{0,0,0,-((variables_2)_(k))_R,-((variables_1)_(k))_R,0,0},{((variables_3)_(k))_R,-((variables_0)_(k))_R,((variables_2)_(k))_R,0,-((variables_5)_(k))_R,-((variables_4)_(k))_R,0}});
        S = for k from g+1 to 2*g list (matrix {{0,0,0,-2*((variables_3)_(k))_R,-2*((variables_2)_(k))_R,-2*((variables_0)_(k))_R,0},{((variables_2)_(k))_R,0,((variables_1)_(k))_R,((variables_5)_(k))_R,0,-((variables_3)_(k))_R,0},{((variables_0)_(k))_R,0,0,((variables_4)_(k))_R,((variables_3)_(k))_R,0,0},{0,0,0,0,0,0,0},{0,0,0,((variables_0)_(k))_R,0,0,0},{0,0,0,-((variables_2)_(k))_R,-((variables_1)_(k))_R,0,0},{((variables_3)_(k))_R,-((variables_0)_(k))_R,((variables_2)_(k))_R,0,-((variables_5)_(k))_R,-((variables_4)_(k))_R,0}});
    )  else if opts.LieType == "CnNil" then ( -- Cn type nilpotent algebras
        -- make lists of variables
        XX = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_0)_(k,i,j);
        YY = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_1)_(k,i,j);
        SS = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_2)_(k,i,j);
        TT = flatten for k from 1 to g list
            flatten for i from 1 to n list for j from i+1 to n list (variables_3)_(k,i,j);
        UU = flatten for k from 1 to g list
            flatten for i from 1 to n list (variables_4)_(k,i);
        VV = flatten for k from 1 to g list
            flatten for i from 1 to n list (variables_5)_(k,i);

        -- construct the ambient ring
        R = opts.CoefficientRing[join(XX, YY, SS, TT, UU, VV)];

        -- make matrices
        X = for k from 1 to g list (
            Xtemp = matrix table (2*n, 2*n, (i,j)->0_R);
            for i from 1 to n do
                for j from i+1 to n do
                    Xtemp = Xtemp + elementaryMatrix((((variables_0)_(k,i,j))_R), 2*n, i, j) + elementaryMatrix(-(((variables_0)_(k,i,j))_R), 2*n, j+n, i+n) + elementaryMatrix((((variables_1)_(k,i,j))_R), 2*n, i, j+n) + elementaryMatrix((((variables_1)_(k,i,j))_R), 2*n, j, i+n);
            for i from 1 to n do
                Xtemp = Xtemp + elementaryMatrix((((variables_4)_(k,i))_R), 2*n, i, i+n);
            Xtemp
            );
        
        S = for k from 1 to g list (
            Xtemp = matrix table (2*n, 2*n, (i,j)->0_R);
            for i from 1 to n do
                for j from i+1 to n do
                    Xtemp = Xtemp + elementaryMatrix((((variables_2)_(k,i,j))_R), 2*n, i, j) + elementaryMatrix(-(((variables_2)_(k,i,j))_R), 2*n, j+n, i+n) + elementaryMatrix((((variables_3)_(k,i,j))_R), 2*n, i, j+n) + elementaryMatrix((((variables_3)_(k,i,j))_R), 2*n, j, i+n);
            for i from 1 to n do
                Xtemp = Xtemp + elementaryMatrix((((variables_5)_(k,i))_R), 2*n, i, i+n);
            Xtemp
            );
    ) else error "The group type is not supported.";
    (X, S)
    )

repHomologyChainLie = method (Options => {
        LieType => "DnNil"
        })
repHomologyChainLie(Matrix, ZZ) := Complex => opts -> (M, matrixSize) -> (
    n := matrixSize; local L; local K;
    if opts.LieType == "DnNil" then (
        return koszulComplex flatten for i from 0 to n-1 list flatten for j from i+1 to n-1 list flatten {M_(i, j), M_(i, j+n)};
    ) else if opts.LieType == "BnNil" then (
        L = flatten for i from 0 to n-1 list flatten for j from i+1 to n-1 list flatten {M_(i, j), M_(i, j+n)};
        K = flatten for i from 0 to n-1 list M_(i, 2*n);
        return koszulComplex join(L, K);
    ) else if opts.LieType == "CnNil" then (
        L = flatten for i from 0 to n-1 list flatten for j from i+1 to n-1 list flatten {M_(i, j), M_(i, j+n)};
        K = flatten for i from 0 to n-1 list M_(i, i+n);
        return koszulComplex join(L, K);
    ) else if opts.LieType == "G2Nil" then (
        return koszulComplex flatten {M_(2,0),M_(1,2),M_(1,0),M_(6,0),M_(2,3),M_(1,3)};
    ) else error "The Lie type is not supported.";
)

surfaceRepHomologyLie = method (Options => options makeMatricesLie)
surfaceRepHomologyLie(ZZ) := opts -> (matrixSize) -> (
    n := matrixSize;
    if (opts.LieType == "gl") or (opts.LieType == "sl") or (opts.LieType == "n") or (opts.LieType == "nilpotent") or (opts.LieType == "b") or (opts.LieType == "borel") then return surfaceRepHomologyAlg(n, 1, CoefficientRing => opts.CoefficientRing, AlgType => opts.LieType, Variables => opts.Variables);
    -- construct the matrices
    (X, S) := makeMatricesLie(n, 1, CoefficientRing => opts.CoefficientRing, LieType => opts.LieType, Variables => opts.Variables);

    -- the matrix for the complex
    M := (X_0 * S_0 - S_0 * X_0);

    -- construct the koszul complex
    C := repHomologyChainLie(M, n, LieType => opts.LieType);

    -- print the result
    printKoszulHH(C)
)

----------------------------------------------------
--Representation homology of links
----------------------------------------------------

-- Give the module structure using the braid element
twistP = method()
twistP(ZZ, List) := List => (i, XL) -> (
    -- XL is a list of n square invertible matrices
    -- 0 < i < n, the action
    n := #XL;
    i = i-1; -- to change to 0-based indexing
    for j from 0 to n-1 list (
        if j == i then XL_i * XL_(i+1) * inverse(XL_i)
        else if j == i+1 then XL_i
        else XL_j
        )
)

twistN = method()
twistN(ZZ, List) := List => (i, XL) -> (
    -- XL is a list of n square invertible matrices
    -- -n < i < 0, the inverse action
    n := #XL;
    i = -i;
    i = i-1; -- to change to 0-based indexing
    for j from 0 to n-1 list (
        if j == i then XL_(i+1)
        else if j == i+1 then ( inverse(XL_(i+1)) * XL_i * XL_(i+1))
        -- There is an annoying label
        else XL_j
    )
)

linkTwist = method()
linkTwist(Link, List) := List => (L, Mat) -> (
    -- Mat is the list of matrices to be changed according to the link
    for n in word (L) do (
        if n > 0 then Mat = twistP(n, Mat)
        else Mat = twistN(n, Mat);
    );
    Mat
)

linkRepHomology = method (Options => options makeMatricesGroup)
linkRepHomology(Link, ZZ) := opts -> (L, matrixSize) -> (
    -- construct the matrices
    (X, Y) := makeMatricesGroup( matrixSize, braidIndex(L), CoefficientRing => opts.CoefficientRing, GroupType => opts.GroupType, Variables => opts.Variables);

    Z := linkTwist(L, Y);
    local lst; local R; local C; local L;

    -- construct the koszul complex
    if opts.GroupType == "GL" then (
        lst = flatten for t from 1 to #X list (
            flatten for i from 0 to matrixSize-1 list
                for j from 0 to matrixSize-1 list (X_(t-1))_(i,j)-(Z_(t-1))_(i,j));
        R = ring X_0 / ideal lst;
        C = koszulComplex matrix {flatten for t from 1 to #X list (
            flatten for i from 0 to matrixSize-1 list
                for j from 0 to matrixSize-1 list ((X_(t-1))_(i,j)-(Y_(t-1))_(i,j))_R)};
    )
    else if opts.GroupType == "SL" then(
        lst = flatten for t from 1 to #X list (
            flatten for i from 0 to matrixSize-1 list
                for j from 0 to matrixSize-1 list (X_(t-1))_(i,j)-(Z_(t-1))_(i,j));
        R = ring X_0 / ideal lst;
        C = koszulComplex matrix {flatten for t from 1 to #X list (
            L = flatten for i from 0 to matrixSize-1 list
                for j from 0 to matrixSize-1 list ((X_(t-1))_(i,j)-(Y_(t-1))_(i,j))_R;
            drop (L,1)
            )};
    )
    else if (opts.GroupType == "U") or (opts.GroupType == "Unipotent") then (
        lst = flatten for t from 1 to #X list (
            flatten for i from 0 to matrixSize-2 list
                for j from i+1 to matrixSize-1 list (X_(t-1))_(i,j)-(Z_(t-1))_(i,j));
        R = ring X_0 / ideal lst;
        C = koszulComplex matrix {flatten for t from 1 to #X list (
            flatten for i from 0 to matrixSize-2 list
                for j from i+1 to matrixSize-1 list ((X_(t-1))_(i,j)-(Y_(t-1))_(i,j))_R)};
    )
    else if (opts.GroupType == "B") or (opts.GroupType == "Borel") then (
        lst = flatten for t from 1 to #X list (
            flatten for i from 0 to matrixSize-1 list
                for j from i to matrixSize-1 list (X_(t-1))_(i,j)-(Z_(t-1))_(i,j));
        R = ring X_0 / ideal lst;
        C = koszulComplex matrix {flatten for t from 1 to #X list (
            flatten for i from 0 to matrixSize-1 list
                for j from i to matrixSize-1 list ((X_(t-1))_(i,j)-(Y_(t-1))_(i,j))_R)};
    ) else error "The group type is not supported.";

    -- print the result
    printKoszulHH(C)
)

-------------------

beginDocumentation()

-- Front Page
doc ///
    Key
        RepHomology
    Headline
        a package for computing representation homology of certain topological spaces
    Description
        Text
            This package {\em RepHomology} provides.
            We also provide a new type @TO "Link"@ with basic operations of topological link (complements).

            {\bf Contributors}:
            @HREF("https://sites.google.com/view/guanyu-li-math/home", "Guanyu Li")@.

            {\bf Other acknowledgements}:

            ----TODO
    SeeAlso
        surfaceRepHomologyGroup
        surfaceRepHomologyAlg
        linkRepHomology
///

doc /// 
    Key
        Link
    Description
        Text
            This class is a type of @TO "MutableHashTable"@ which represents a link complement in $\mathbb{R}^3$.
        Example
            L = link (2, {1,1,1});
    SeeAlso
        link
        isWellDefined
        Trefoil
        FigureEight
///

doc /// 
    Key
        braidIndex
        (braidIndex, Link)
    Headline
        The braid index of a link
    Description
        Text
            This is the function returning the braid index of a Link object.
        Example
            braidIndex(FigureEight)
    SeeAlso
        link
        Trefoil
        FigureEight
///

doc /// 
    Key
        word
        (word, Link)
    Headline
        The braid word of a link
    Description
        Text
            This is the function returning the braid word of a Link object.
        Example
            word(FigureEight)
    SeeAlso
        link
        Trefoil
        FigureEight
///

doc ///
    Key
        link
        (link, ZZ, List)
    Headline
        creates a new Link object
    Description
        Text
            This class is a type of @TO "HashTable"@ which represents finite posets. It consists
            of a natural number called the braid index, and a list of integers representing the braid operations.
        Example
            n = 2;                  -- the braid index of the link
            w = {1,1,1};  -- a list of braid operations, for this list it means $\sigma_1^3$
            L = link(n, w)                 -- the link constructed
    SeeAlso
        Link
///

doc ///
    Key
        Trefoil
    Headline
        Link object trefoil
    Description
        Text
            The Link object representing the trefoil knot complement
    SeeAlso
        Link
        FigureEight
///

doc ///
    Key
        FigureEight
    Headline
        Link object figure-eight
    Description
        Text
            The Link object representing the figure-eight knot complement
    SeeAlso
        Link
        Trefoil
///

doc ///
    Key
        isWellDefined
        (isWellDefined, Link)
    Headline
        whether a link is well-defined
    Description
        Text
            This routine checks if a constructed link is well-defined, namely, whether the braid operations are controled by the braid index.
        Example
            isWellDefined (Trefoil)
            isWellDefined link (2, {1,2,1})
            isWellDefined link (2, {1,0,1})
            isWellDefined link (3, {1,2,-1,-3})
    SeeAlso
        Link
///

doc ///
    Key
        surfaceRepHomologyGroup
        (surfaceRepHomologyGroup, ZZ, ZZ)
        [surfaceRepHomologyGroup, CoefficientRing]
        [surfaceRepHomologyGroup, Homogenize]
        [surfaceRepHomologyGroup, GroupType]
    Headline
        Compute group type representation homology of surface
    Description
        Text
             This is the function to compute group type representation homology of surface directly. There are two inputs, the size of matrices $n$ and the genus $g$ of
        Example
            surfaceRepHomologyGroup(2,1)
    SeeAlso
        surfaceRepHomologyAlg
///

doc ///
    Key
        surfaceRepHomologyAlg
        (surfaceRepHomologyAlg, ZZ, ZZ)
        [surfaceRepHomologyAlg, CoefficientRing]
        [surfaceRepHomologyAlg, Homogenize]
        [surfaceRepHomologyAlg, AlgType]
    Headline
        Compute algebra type representation homology of surface
    Description
        Text
            The
        Example
            surfaceRepHomologyAlg(2, 1, AlgType=>"n")
    SeeAlso
        surfaceRepHomologyGroup
///

doc ///
    Key
        surfaceRepHomologyLie
        (surfaceRepHomologyLie, ZZ)
        [surfaceRepHomologyLie, CoefficientRing]
        [surfaceRepHomologyLie, LieType]
    Headline
        Compute representation homology of link (complement in $\mathbb{R}^3$)
    Description
        Text
            The
        Example
            surfaceRepHomologyLie(3,LieType=>"n")
        Text
            This includes other special types of Lie algebras:
        Example
            surfaceRepHomologyLie(2,LieType=>"G2Nil")
    SeeAlso
        surfaceRepHomologyAlg
///

doc ///
    Key
        linkRepHomology
        (linkRepHomology, Link, ZZ)
        [linkRepHomology, CoefficientRing]
        [linkRepHomology, Homogenize]
        [linkRepHomology, GroupType]
    Headline
        Compute representation homology of link (complement in $\mathbb{R}^3$)
    Description
        Text
            The
        Example
            linkRepHomology(Trefoil,3,GroupType=>"U")
    SeeAlso
        Link
///

TEST ///
(M1, M2) = makeMatricesGroup(kk, "Unipotent", {x,y,s,t}, {5,1})
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 5)
assert(numrows M1#0 == 5)
assert(numcols M2#0 == 5)
assert(numrows M2#0 == 5)
assert(ring M1#0 === ring M2#0)
assert(M1#0 == matrix {
            {1, x_(1,1,2), x_(1,1,3), x_(1,1,4), x_(1,1,5)},
            {0, 1, x_(1,2,3), x_(1,2,4), x_(1,2,5)},
            {0, 0, 1, x_(1,3,4), x_(1,3,5)},
            {0, 0, 0, 1, x_(1,4,5)},
            {0, 0, 0, 0, 1}})

(M1, M2) = makeMatricesGroup(5, 1, CoefficientRing => QQ, Group => "U", Homogenize => true )
assert isHomogeneous ideal(M1#0 * M2#0 - M2#0 * M1#0)
///

end--