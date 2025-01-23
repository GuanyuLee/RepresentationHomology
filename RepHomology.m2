-*
   Copyright 2024, .
*-

newPackage(
    "RepHomology",
    Version => "1.0",
    Date => "December, 2024",
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
    "surfaceRepHomologyComplexGroup",
    "surfaceRepHomologyAlg",
    "surfaceRepHomologyComplexAlg",
    "torusRepHomologyLie",
    "torusRepHomologyComplexLie",
    "link",
    "linkRepHomology",
    "linkRepHomologyComplex",
    "word",
    "braidIndex",
    -- types
    "GroupType",
    "AlgType",
    "LieType",
    "Homogenize",
    "Link",
    "BraidIndex",
    "LinkWord",
    "Trefoil",
    "FigureEight"
    }

-------------------
--The type Link
-------------------

Link = new Type of HashTable
Link.synonym = "link"
  -- key:
  -- BraidIndex : an positive integer denoting the braid index
  -- LinkWord : the link word for the link, a list of nonzero integers representing the braid operations. For instance, the list {1,1,1} is $\sigma_1^3$, meaning braid the 1st and the 2nd stand three times.
  -- Use nagative integer denoting the inverse braiding.

Link.GlobalAssignHook = globalAssignFunction
Link.GlobalReleaseHook = globalReleaseFunction

protect BraidIndex
protect LinkWord

-- Construct a link
link = method()
link (ZZ, List) := (n,w) -> (
    if n<=0 then error "The braid index should be a positive integer";
    for o in w do (
        if (o == 0) then error "The braid operation cannot be 0.";
        if (o > n-1) or ((-o) > n-1) then error "The braid operations should be within the braids, i.e. the absolute value of the operation integer should be smaller than the braid index.";
    );
	new Link from {
        symbol BraidIndex => n,
        symbol LinkWord => w
	}
)

braidIndex = method()
braidIndex (Link) := (l) -> (l.BraidIndex)

word = method()
word (Link) := (l) -> (l.LinkWord)

-- unlink is represented by the empty link
isWellDefined (Link) := Boolean => (l) -> (
    if braidIndex(l)<=0 then return false;
    for n in word(l) do (
        if (n == 0) then return false;
        if (n > braidIndex(l)-1) or ((-n) > braidIndex(l)-1) then return false;
    );
    true
)

Trefoil = link (2,{1,1,1});
FigureEight = link (3,{1,-2,1,-2});

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
    ) else error "The group type is not supported. It should be one of \" GL \",  \" SL \", \" U \", or  \" B \" .";
    (Xnew, Ynew)
    )

-- To construct the chain complex computing the representation homology, private function
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
    ) else error "The group type is not supported. It should be one of \" GL \",  \" SL \", \" U \", or  \" B \" .";
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

-- Compute the representation homology of surfaces of group type directly
-* 
Inputs:
CoefficientRing : ground ring
matrixSize : size of matrices
genusOfSurface : genus of the commuting variety
GroupType : type of the group scheme, a string, including "B", "Borel", "U", "Unipotent", "GL" and "SL"
*-
surfaceRepHomologyGroup = method (Options => options makeMatricesGroup)
surfaceRepHomologyGroup(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    if ((n<=0) or (g<=0)) then error "The size of matrices and genus need to be positive integers";
    -- construct the matrices
    (X, Y) := makeMatricesGroup(n, g, CoefficientRing => opts.CoefficientRing, GroupType => opts.GroupType, Variables => opts.Variables);

    -- the matrix for the complex
    M := product for k from 0 to g-1 list (X_k * Y_k * inverse(X_k) * inverse(Y_k));

    -- construct the koszul complex
    C := surfaceRepHomologyChainGroup(M, n, g, GroupType => opts.GroupType);

    -- print the result
    printKoszulHH(C)
)

-- Almost the same function as before
-- but return the chain complex
surfaceRepHomologyComplexGroup = method (Options => options makeMatricesGroup)
surfaceRepHomologyComplexGroup(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    if ((n<=0) or (g<=0)) then error "The size of matrices and genus need to be positive integers";
    -- construct the matrices
    (X, Y) := makeMatricesGroup(n, g, CoefficientRing => opts.CoefficientRing, GroupType => opts.GroupType, Variables => opts.Variables);

    -- the matrix for the complex
    M := product for k from 0 to g-1 list (X_k * Y_k * inverse(X_k) * inverse(Y_k));

    -- construct the koszul complex
    surfaceRepHomologyChainGroup(M, n, g, GroupType => opts.GroupType)
)

----------------------------------------------------
--Algebra version of representation homology of surfaces
----------------------------------------------------

-- The computation pattern is the same as the previous part
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
    ) else error "The algebra type is not supported. It should be one of \" gl \",  \" sl \", \" n \", or  \" b \" .";
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
    ) else error "The algebra type is not supported. It should be one of \" gl \",  \" sl \", \" n \", or  \" b \" .";
)

-- Direct computation of the representation homology of surfaces of algebra type
-* 
Inputs:
CoefficientRing : ground ring
matrixSize : size of matrices
genusOfSurface : genus of the commuting variety
AlgType : type of the group scheme, a string, including "b", "borel", "n", "nilpotent", "gl" and "sl"
*-
surfaceRepHomologyAlg = method (Options => options makeMatricesAlg)
surfaceRepHomologyAlg(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    if ((n<=0) or (g<=0)) then error "The size of matrices and genus need to be positive integers";
    -- construct the matrices
    (X, Y) := makeMatricesAlg(n, g, CoefficientRing => opts.CoefficientRing, AlgType => opts.AlgType, Variables => opts.Variables);

    -- the matrix for the complex
    M := sum for k from 0 to g-1 list (X_k * Y_k - Y_k * X_k);

    -- construct the koszul complex
    C := surfaceRepHomologyChainAlg(M, n, g, AlgType => opts.AlgType);

    -- print the result
    printKoszulHH(C)
)

-- Return the chain complex instead
surfaceRepHomologyComplexAlg = method (Options => options makeMatricesAlg)
surfaceRepHomologyComplexAlg(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    if ((n<=0) or (g<=0)) then error "The size of matrices and genus need to be positive integers";
    -- construct the matrices
    (X, Y) := makeMatricesAlg(n, g, CoefficientRing => opts.CoefficientRing, AlgType => opts.AlgType, Variables => opts.Variables);

    -- the matrix for the complex
    M := sum for k from 0 to g-1 list (X_k * Y_k - Y_k * X_k);

    -- construct the koszul complex
    surfaceRepHomologyChainAlg(M, n, g, AlgType => opts.AlgType)
)

----------------------------------------------------
--Lie algebra version of representation homology of surfaces
----------------------------------------------------

-- Most of the result can be deduced by last part, we provide some more Lie algebra coefficients - maximal nilpotent subalgebra of semisimple algebras
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
        LieType => "gl",
        Homogenize => false,
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
    ) else error "The group type is not supported. It should be one of \" gl \",  \" sl \", \" n \", \" b\", or \" DnNil \", \" BnNil \", \" CnNil \".";
    (X, S)
    )

torusRepChainLie = method (Options => {
        LieType => "DnNil"
        })
torusRepChainLie(Matrix, ZZ) := Complex => opts -> (M, matrixSize) -> (
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
    ) else error "The group type is not supported. It should be one of \" gl \",  \" sl \", \" n \", \" b\", or \" DnNil \", \" BnNil \", \" CnNil \", and \" G2Nil\".";
)

-- Direct computation of the representation homology of torus of Lie type
-* 
Inputs:
CoefficientRing : ground ring
matrixSize : size of matrices
genusOfSurface : genus of the commuting variety
LieType : type of the group scheme, a string, including "b", "borel", "n", "nilpotent", "gl" and "sl", or "DnNil", "BnNil", "CnNil", and "G2Nil"
*-
torusRepHomologyLie = method (Options => options makeMatricesLie)
torusRepHomologyLie(ZZ) := opts -> (matrixSize) -> (
    n := matrixSize;
    if (n<=0) then error "The size of matrices needs to be a positive integer";
    if (opts.LieType == "gl") or (opts.LieType == "sl") or (opts.LieType == "n") or (opts.LieType == "nilpotent") or (opts.LieType == "b") or (opts.LieType == "borel") then return surfaceRepHomologyAlg(n, 1, CoefficientRing => opts.CoefficientRing, AlgType => opts.LieType, Variables => opts.Variables);
    -- construct the matrices
    (X, S) := makeMatricesLie(n, 1, CoefficientRing => opts.CoefficientRing, LieType => opts.LieType, Variables => opts.Variables);

    -- the matrix for the complex
    M := (X_0 * S_0 - S_0 * X_0);

    -- construct the koszul complex
    C := torusRepChainLie(M, n, LieType => opts.LieType);

    -- print the result
    printKoszulHH(C)
)

torusRepHomologyComplexLie = method (Options => options makeMatricesLie)
torusRepHomologyComplexLie(ZZ) := opts -> (matrixSize) -> (
    n := matrixSize;
    if (n<=0) then error "The size of matrices needs to be a positive integer";
    if (opts.LieType == "gl") or (opts.LieType == "sl") or (opts.LieType == "n") or (opts.LieType == "nilpotent") or (opts.LieType == "b") or (opts.LieType == "borel") then return surfaceRepHomologyAlg(n, 1, CoefficientRing => opts.CoefficientRing, AlgType => opts.LieType, Variables => opts.Variables);
    -- construct the matrices
    (X, S) := makeMatricesLie(n, 1, CoefficientRing => opts.CoefficientRing, LieType => opts.LieType, Variables => opts.Variables);

    -- the matrix for the complex
    M := (X_0 * S_0 - S_0 * X_0);

    -- construct the koszul complex
    torusRepChainLie(M, n, LieType => opts.LieType)
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

linkRepChain = method (Options => {
        GroupType => "GL"
        })
linkRepChain(Link, List, List, ZZ) := Complex => opts -> (L, matriceListX, matriceListY, matrixSize) -> (
    if (not isWellDefined(L)) then error "The link is not well-defined";
    X := matriceListX; Y := matriceListY;
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
    ) else error "The group type is not supported. It should be one of \" GL \",  \" SL \", \" U \", or  \" B \" .";
    C
)

-- Direct computation of the representation homology of link
-* 
Inputs:
CoefficientRing : ground ring
matrixSize : size of matrices
genusOfSurface : genus of the commuting variety
GroupType : type of the group scheme, a string, including "B", "Borel", "U", "Unipotent", "GL" and "SL"
*-
linkRepHomology = method (Options => options makeMatricesGroup)
linkRepHomology(Link, ZZ) := opts -> (L, matrixSize) -> (
    -- construct the matrices
    if (matrixSize<=0) then error "The size of matrices needs to be a positive integer";
    (X, Y) := makeMatricesGroup( matrixSize, braidIndex(L), CoefficientRing => opts.CoefficientRing, GroupType => opts.GroupType, Variables => opts.Variables);

    -- construct the complex
    C := linkRepChain(L, X, Y, matrixSize, GroupType => opts.GroupType);

    -- print the result
    printKoszulHH(C)
)

linkRepHomologyComplex = method (Options => options makeMatricesGroup)
linkRepHomologyComplex(Link, ZZ) := opts -> (L, matrixSize) -> (
    -- construct the matrices
    if (matrixSize<=0) then error "The size of matrices needs to be a positive integer";
    (X, Y) := makeMatricesGroup( matrixSize, braidIndex(L), CoefficientRing => opts.CoefficientRing, GroupType => opts.GroupType, Variables => opts.Variables);

    -- construct the complex
    linkRepChain(L, X, Y, matrixSize, GroupType => opts.GroupType)
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
            This package {\em RepHomology} provides direct computation of representation homology of certain spaces, such as surfaces and link (complements). Some analogies can be computed as well.
            We also provide a new type @TO Link @ with basic operations of topological link (complements).

            {\bf Authors}:
            @HREF("https://sites.google.com/view/guanyu-li-math/home", "Guanyu Li")@.

            {\bf Other acknowledgements}:
                Many methods were discussed with Mike Stillman, and there are many useful suggestions implemented in this package.
            ----TODO
    SeeAlso
        surfaceRepHomologyGroup
        surfaceRepHomologyAlg
        torusRepHomologyLie
        linkRepHomology
///

doc /// 
    Key
        Link
    Headline
        a type to represent a link complement in $\mathbb{R}^3$
    Description
        Text
            This class is a type of @TO "HashTable"@ which represents a link complement in $\mathbb{R}^3$.
        Example
            L = link (2, {1,1,1});
            L = link (1, {}); -- Unknot
    SeeAlso
        link
        (isWellDefined, Link)
        Trefoil
        FigureEight
///

doc /// 
    Key
        braidIndex
        (braidIndex, Link)
    Headline
        The braid index of a link
    Usage
        n = braidIndex(L)
    Inputs
        L : Link
    Outputs
        n : ZZ
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
    Usage
        w = word(L)
    Inputs
        L : Link
    Outputs
        w : List
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
    Usage
        L = link(n, w)
    Inputs
        n : ZZ
        w : List
    Outputs
        L : Link
    Description
        Text
            This class is a type of @TO "HashTable"@ which represents a link complement. It consists
            of a natural number called the braid index, and a list of integers representing the braid operations. For instance, the link word {1,1,1} is $\sigma_1^3$, meaning braid the 1st and the 2nd stand three times.
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
        Example
            Trefoil
            braidIndex(Trefoil)
            word(Trefoil)
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
        Example
            FigureEight
            braidIndex(FigureEight)
            word(FigureEight)
    SeeAlso
        Link
        Trefoil
///

doc ///
    Key
        (isWellDefined, Link)
    Headline
        To test whether a link is well-defined
    Description
        Text
            This routine checks if a constructed link is well-defined, namely, whether the braid operations are valid under the braid index.
        Example
            isWellDefined Trefoil
    SeeAlso
        Link
///

doc ///
    Key
        GroupType
    Headline
        an optional argument
    Description
        Text
            A symbol used as the name of an optional argument.
    SeeAlso
        surfaceRepHomologyGroup
        surfaceRepHomologyComplexGroup
        linkRepHomology
///

doc ///
    Key
        AlgType
    Headline
        an optional argument
    Description
        Text
            A symbol used as the name of an optional argument.
    SeeAlso
        surfaceRepHomologyAlg
        surfaceRepHomologyComplexAlg
///

doc ///
    Key
        LieType
    Headline
        an optional argument
    Description
        Text
            A symbol used as the name of an optional argument.
    SeeAlso
        torusRepHomologyLie
        torusRepHomologyComplexLie
///

doc ///
    Key
        Homogenize
    Headline
        an optional argument
    Description
        Text
            A symbol used as the name of an optional argument.
    SeeAlso
        surfaceRepHomologyGroup
        surfaceRepHomologyAlg
        torusRepHomologyLie
        linkRepHomology
///

doc ///
    Key
        surfaceRepHomologyGroup
        (surfaceRepHomologyGroup, ZZ, ZZ)
    Headline
        Compute group type representation homology of a surface
    Usage
        lst = surfaceRepHomologyGroup(matrixSize, genus)
    Inputs
        matrixSize : ZZ
        genus : ZZ
    Outputs
        lst : List
    Description
        Text
             This is the function to compute group type representation homology of surface directly. There are two inputs, the size of matrices $n$ and the genus $g$ of the surface.
             One could also change the coefficient ring and the group type. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            surfaceRepHomologyGroup(2, 1)
            surfaceRepHomologyGroup(2, 1, GroupType=>"B")
            surfaceRepHomologyGroup(4, 1, GroupType=>"U", CoefficientRing=>ZZ/101, Homogenize=>true)
    SeeAlso
        surfaceRepHomologyAlg
        surfaceRepHomologyComplexGroup
///

doc ///
    Key
        surfaceRepHomologyComplexGroup
        (surfaceRepHomologyComplexGroup, ZZ, ZZ)
    Headline
        Compute group type representation homology chain complex of a surface
    Usage
        C = surfaceRepHomologyComplexGroup(matrixSize, genus)
    Inputs
        matrixSize : ZZ
        genus : ZZ
    Outputs
        C : Complex
    Description
        Text
             This is the function to return the chain complex computing the group type representation homology of surface. There are two inputs, the size of matrices 'matrixSize' and the genus 'genus' of the surface.
             One could also change the coefficient ring and the group type. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            surfaceRepHomologyComplexGroup(2, 1)
            surfaceRepHomologyComplexGroup(2, 1, GroupType=>"B")
            surfaceRepHomologyComplexGroup(4, 1, GroupType=>"U", CoefficientRing=>ZZ/101, Homogenize=>true)
    SeeAlso
        surfaceRepHomologyGroup
///

doc ///
    Key
        [surfaceRepHomologyGroup, GroupType]
    Headline
        Option to change the group coefficient type
    Usage
        lst =  surfaceRepHomologyGroup(matrixSize, genus, GroupType=>s)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        s : String
    Outputs
        lst : List
    Description
        Text
            This is the option to change the group type coefficient. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            surfaceRepHomologyGroup(2, 1, GroupType=>"B")
///

doc ///
    Key
        [surfaceRepHomologyComplexGroup, GroupType]
    Headline
        Option to change the group coefficient type
    Usage
        C =  surfaceRepHomologyComplexGroup(matrixSize, genus, GroupType=>s)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        s : String
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the group type coefficient. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            surfaceRepHomologyComplexGroup(2, 1, GroupType=>"B")
///

doc ///
    Key
        [surfaceRepHomologyGroup, CoefficientRing]
    Headline
        Option to change the ground ring of the group coefficient
    Usage
        lst =  surfaceRepHomologyGroup(matrixSize, genus, CoefficientRing=>kk)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        kk : Ring
    Outputs
        lst : List
    Description
        Text
            This is the option to change the ground ring of the group type coefficient. The default value is $\mathbb{Q}$.
        Example
            surfaceRepHomologyGroup(2, 1, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [surfaceRepHomologyComplexGroup, CoefficientRing]
    Headline
        Option to change the ground ring of the group coefficient
    Usage
        C =  surfaceRepHomologyComplexGroup(matrixSize, genus, CoefficientRing=>kk)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        kk : Ring
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the ground ring of the group type coefficient. The default value is $\mathbb{Q}$.
        Example
            surfaceRepHomologyComplexGroup(2, 1, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [surfaceRepHomologyGroup, Homogenize]
    Headline
        Option to determine whether the group coefficient is homogeneous
    Usage
        lst =  surfaceRepHomologyGroup(matrixSize, genus, Homogenize=>B)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        B : Boolean
    Outputs
        lst : List
    Description
        Text
            When the group type is Borel or unipotent, the group coefficient could be set homogeneous. This is the option to set whether the group coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the group is homogeneous.
        Example
            surfaceRepHomologyGroup(3, 1, GroupType=>"U", Homogenize=>true)
///

doc ///
    Key
        [surfaceRepHomologyComplexGroup, Homogenize]
    Headline
        Option to determine whether the group coefficient is homogeneous
    Usage
        C =  surfaceRepHomologyComplexGroup(matrixSize, genus, Homogenize=>B)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        B : Boolean
    Outputs
        C : Complex
    Description
        Text
            When the group type is Borel or unipotent, the group coefficient could be set homogeneous. This is the option to set whether the group coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the group is homogeneous.
        Example
            surfaceRepHomologyComplexGroup(3, 1, GroupType=>"U", Homogenize=>true)
///

doc ///
    Key
        surfaceRepHomologyAlg
        (surfaceRepHomologyAlg, ZZ, ZZ)
    Headline
        Compute algebra type representation homology of a surface
    Usage
        lst = surfaceRepHomologyAlg(matrixSize, genus)
    Inputs
        matrixSize : ZZ
        genus : ZZ
    Outputs
        lst : List
    Description
        Text
             This is the function to compute algebra type representation homology of a surface directly. There are two inputs, the size of matrices $n$ and the genus $g$ of the surface.
             One could also change the coefficient ring and the algebra type. A algebra type could be "gl" (default), "sl", "borel" ("b" for short), or "nilpotent" ("n" for short).
        Example
            surfaceRepHomologyAlg(2, 1)
            surfaceRepHomologyAlg(2, 1, AlgType=>"b")
            surfaceRepHomologyAlg(4, 1, AlgType=>"n", CoefficientRing=>ZZ/101, Homogenize=>true)
    SeeAlso
        surfaceRepHomologyGroup
        surfaceRepHomologyComplexAlg
        torusRepHomologyLie
///

doc ///
    Key
        surfaceRepHomologyComplexAlg
        (surfaceRepHomologyComplexAlg, ZZ, ZZ)
    Headline
        Compute algebra type representation homology of a surface
    Usage
        C = surfaceRepHomologyComplexAlg(matrixSize, genus)
    Inputs
        matrixSize : ZZ
        genus : ZZ
    Outputs
        C : Complex
    Description
        Text
             This is the function to return the chain complex computing the algebra type representation homology of a surface. There are two inputs, the size of matrices $n$ and the genus $g$ of the surface.
             One could also change the coefficient ring and the algebra type. A algebra type could be "gl" (default), "sl", "borel" ("b" for short), or "nilpotent" ("n" for short).
        Example
            surfaceRepHomologyComplexAlg(2, 1)
            surfaceRepHomologyComplexAlg(2, 1, AlgType=>"b")
            surfaceRepHomologyComplexAlg(4, 1, AlgType=>"n", CoefficientRing=>ZZ/101, Homogenize=>true)
    SeeAlso
        surfaceRepHomologyAlg
        surfaceRepHomologyComplexGroup
        torusRepHomologyComplexLie
///

doc ///
    Key
        [surfaceRepHomologyAlg, AlgType]
    Headline
        Option to change the algebra coefficient type
    Usage
        lst =  surfaceRepHomologyAlg(matrixSize, genus, AlgType=>s)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        s : String
    Outputs
        lst : List
    Description
        Text
            This is the option to change the algebra type coefficient. An algebra type could be "gl" (default), "sl", "borel" ("b" for short), or "nilpotent" ("n" for short).
        Example
            surfaceRepHomologyAlg(2, 1, AlgType=>"b")
///

doc ///
    Key
        [surfaceRepHomologyComplexAlg, AlgType]
    Headline
        Option to change the algebra coefficient type
    Usage
        C =  surfaceRepHomologyComplexAlg(matrixSize, genus, AlgType=>s)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        s : String
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the algebra type coefficient. An algebra type could be "gl" (default), "sl", "borel" ("b" for short), or "nilpotent" ("n" for short).
        Example
            surfaceRepHomologyComplexAlg(2, 1, AlgType=>"b")
///

doc ///
    Key
        [surfaceRepHomologyAlg, CoefficientRing]
    Headline
        Option to change the ground ring of the algebra coefficient
    Usage
        lst =  surfaceRepHomologyAlg(matrixSize, genus, CoefficientRing=>kk)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        kk : Ring
    Outputs
        lst : List
    Description
        Text
            This is the option to change the ground ring of the algebra type coefficient. The default value is $\mathbb{Q}$.
        Example
            surfaceRepHomologyAlg(2, 1, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [surfaceRepHomologyComplexAlg, CoefficientRing]
    Headline
        Option to change the ground ring of the algebra coefficient
    Usage
        C =  surfaceRepHomologyComplexAlg(matrixSize, genus, CoefficientRing=>kk)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        kk : Ring
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the ground ring of the algebra type coefficient. The default value is $\mathbb{Q}$.
        Example
            surfaceRepHomologyComplexAlg(2, 1, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [surfaceRepHomologyAlg, Homogenize]
    Headline
        Option to determine whether the algebra coefficient is homogeneous
    Usage
        lst =  surfaceRepHomologyAlg(matrixSize, genus, Homogenize=>B)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        B : Boolean
    Outputs
        lst : List
    Description
        Text
            When the algebra type is Borel or nilpotent, the algebra coefficient could be set homogeneous. This is the option to set whether the algebra coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the algebra is homogeneous.
        Example
            surfaceRepHomologyAlg(3, 1, AlgType=>"n", Homogenize=>true)
///

doc ///
    Key
        [surfaceRepHomologyComplexAlg, Homogenize]
    Headline
        Option to determine whether the algebra coefficient is homogeneous
    Usage
        C =  surfaceRepHomologyComplexAlg(matrixSize, genus, Homogenize=>B)
    Inputs
        matrixSize : ZZ
        genus : ZZ
        B : Boolean
    Outputs
        C : Complex
    Description
        Text
            When the algebra type is Borel or unipotent, the algebra coefficient could be set homogeneous. This is the option to set whether the algebra coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the algebra is homogeneous.
        Example
            surfaceRepHomologyComplexAlg(3, 1, AlgType=>"n", Homogenize=>true)
///

doc ///
    Key
        torusRepHomologyLie
        (torusRepHomologyLie, ZZ)
    Headline
        Compute Lie algebra type representation homology of the torus
    Usage
        lst = torusRepHomologyLie(matrixSize)
    Inputs
        matrixSize : ZZ
    Outputs
        lst : List
    Description
        Text
             This is the function to compute Lie algebra type representation homology of the torus directly. There is one input, the size of matrices $n$.
             One could also change the coefficient ring and the algebra type. A algebra type could be "gl" (default), "sl", "borel" ("b" for short), or "nilpotent" ("n" for short).
        Example
            torusRepHomologyLie(2)
        Text
            The coefficients could be other special types of Lie algebras, including "BnNil", "CnNil", "DnNil", and "G2Nil":
        Example
            torusRepHomologyLie(2,LieType=>"G2Nil")
    SeeAlso
        surfaceRepHomologyGroup
        surfaceRepHomologyAlg
        torusRepHomologyComplexLie
///

doc ///
    Key
        torusRepHomologyComplexLie
        (torusRepHomologyComplexLie, ZZ)
    Headline
        Compute Lie algebra type representation homology of the torus
    Usage
        C = torusRepHomologyComplexLie(matrixSize)
    Inputs
        matrixSize : ZZ
    Outputs
        C : Complex
    Description
        Text
             This is the function to return the chain complex computing the algebra type representation homology of a surface. There is one input, the size of matrices $n$.
             One could also change the coefficient ring and the algebra type. A algebra type could be "gl" (default), "sl", "borel" ("b" for short), or "nilpotent" ("n" for short).
        Example
            torusRepHomologyComplexLie(2)
        Text
            The coefficients could be other special types of Lie algebras, including "BnNil", "CnNil", "DnNil", and "G2Nil":
        Example
            torusRepHomologyComplexLie(2,LieType=>"G2Nil")
    SeeAlso
        surfaceRepHomologyComplexGroup
        surfaceRepHomologyComplexAlg
        torusRepHomologyLie
///

doc ///
    Key
        [torusRepHomologyLie, LieType]
    Headline
        Option to change the Lie algebra coefficient type
    Usage
        lst =  torusRepHomologyLie(matrixSize, LieType=>s)
    Inputs
        matrixSize : ZZ
        s : String
    Outputs
        lst : List
    Description
        Text
            This is the option to change the Lie algebra type coefficient. A Lie algebra type could be "gl" (default), "sl", "borel" ("b" for short), and "nilpotent" ("n" for short), or "BnNil", "CnNil", "DnNil", "G2Nil".
        Example
            torusRepHomologyLie(2, LieType=>"b")
///

doc ///
    Key
        [torusRepHomologyComplexLie, LieType]
    Headline
        Option to change the Lie algebra coefficient type
    Usage
        C =  torusRepHomologyComplexLie(matrixSize, LieType=>s)
    Inputs
        matrixSize : ZZ
        s : String
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the Lie algebra type coefficient. A Lie algebra type could be "gl" (default), "sl", "Borel" ("b" for short), and "nilpotent" ("n" for short), or "BnNil", "CnNil", "DnNil", "G2Nil".
        Example
            torusRepHomologyComplexLie(2, LieType=>"b")
///

doc ///
    Key
        [torusRepHomologyLie, CoefficientRing]
    Headline
        Option to change the ground ring of the Lie algebra coefficient
    Usage
        lst =  torusRepHomologyLie(matrixSize, CoefficientRing=>kk)
    Inputs
        matrixSize : ZZ
        kk : Ring
    Outputs
        lst : List
    Description
        Text
            This is the option to change the ground ring of the Lie algebra type coefficient. The default value is $\mathbb{Q}$.
        Example
            torusRepHomologyLie(2, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [torusRepHomologyComplexLie, CoefficientRing]
    Headline
        Option to change the ground ring of the Lie algebra coefficient
    Usage
        C =  torusRepHomologyComplexLie(matrixSize, CoefficientRing=>kk)
    Inputs
        matrixSize : ZZ
        kk : Ring
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the ground ring of the Lie algebra type coefficient. The default value is $\mathbb{Q}$.
        Example
            torusRepHomologyComplexLie(2, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [torusRepHomologyLie, Homogenize]
    Headline
        Option to determine whether the algebra coefficient is homogeneous
    Usage
        lst =  torusRepHomologyLie(matrixSize, Homogenize=>B)
    Inputs
        matrixSize : ZZ
        B : Boolean
    Outputs
        lst : List
    Description
        Text
            When the Lie algebra type is borel or nilpotent, the algebra coefficient could be set homogeneous. This is the option to set whether the algebra coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the algebra is homogeneous.
        Example
            torusRepHomologyLie(3, LieType=>"n", Homogenize=>true)
///

doc ///
    Key
        [torusRepHomologyComplexLie, Homogenize]
    Headline
        Option to determine whether the algebra coefficient is homogeneous
    Usage
        C =  torusRepHomologyComplexLie(matrixSize, Homogenize=>B)
    Inputs
        matrixSize : ZZ
        B : Boolean
    Outputs
        C : Complex
    Description
        Text
            When the Lie algebra type is borel or unipotent, the algebra coefficient could be set homogeneous. This is the option to set whether the algebra coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the algebra is homogeneous.
        Example
            torusRepHomologyComplexLie(3, LieType=>"n", Homogenize=>true)
///

doc ///
    Key
        linkRepHomology
        (linkRepHomology, Link, ZZ)
    Headline
        Compute representation homology of link (complement in $\mathbb{R}^3$)
    Usage
        lst = linkRepHomology(L, matrixSize)
    Inputs
        L : Link
        matrixSize : ZZ
    Outputs
        lst : List
    Description
        Text
             This is the function to compute group type representation homology of a link $L$ directly. There are two inputs, the link $L$ and the size of matrices $n$.
             One could also change the coefficient ring and the group type. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            linkRepHomology(link(1,{}),2)
    SeeAlso
        Link
        linkRepHomologyComplex
        surfaceRepHomologyGroup
///

doc ///
    Key
        linkRepHomologyComplex
        (linkRepHomologyComplex, Link, ZZ)
    Headline
        Compute representation homology of link (complement in $\mathbb{R}^3$)
    Usage
        C = linkRepHomologyComplex(L, matrixSize)
    Inputs
        L : Link
        matrixSize : ZZ
    Outputs
        C : Complex
    Description
        Text
            This is the function to return the chain complex computing the group type representation homology of a link $L$. There are two inputs, the link $L$ and the size of matrices $n$.
            One could also change the coefficient ring and the group type. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            linkRepHomologyComplex(link(1,{}),2)
    SeeAlso
        Link
        linkRepHomology
        surfaceRepHomologyGroup
///

doc ///
    Key
        [linkRepHomology, GroupType]
    Headline
        Option to change the group coefficient type
    Usage
        lst = linkRepHomology(L, matrixSize, GroupType=>s)
    Inputs
        L : Link
        matrixSize : ZZ
        s : String
    Outputs
        lst : List
    Description
        Text
            This is the option to change the group type coefficient. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            linkRepHomology(Trefoil, 3, GroupType=>"U")
///

doc ///
    Key
        [linkRepHomologyComplex, GroupType]
    Headline
        Option to change the group coefficient type
    Usage
        C =  linkRepHomologyComplex(L, matrixSize, GroupType=>s)
    Inputs
        L : Link
        matrixSize : ZZ
        s : String
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the group type coefficient. A group type could be "GL" (default), "SL", "Borel" ("B" for short), or "Unipotent" ("U" for short).
        Example
            linkRepHomologyComplex(Trefoil, 3, GroupType=>"U")
///

doc ///
    Key
        [linkRepHomology, CoefficientRing]
    Headline
        Option to change the ground ring of the group coefficient
    Usage
        lst =  linkRepHomology(L, matrixSize, CoefficientRing=>kk)
    Inputs
        L : Link
        matrixSize : ZZ
        kk : Ring
    Outputs
        lst : List
    Description
        Text
            This is the option to change the ground ring of the group type coefficient. The default value is $\mathbb{Q}$.
        Example
            linkRepHomology(link(1,{}), 2, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [linkRepHomologyComplex, CoefficientRing]
    Headline
        Option to change the ground ring of the group coefficient
    Usage
        C = linkRepHomologyComplex(L, matrixSize, CoefficientRing=>kk)
    Inputs
        L : Link
        matrixSize : ZZ
        kk : Ring
    Outputs
        C : Complex
    Description
        Text
            This is the option to change the ground ring of the group type coefficient. The default value is $\mathbb{Q}$.
        Example
            linkRepHomologyComplex(link(1,{}), 2, CoefficientRing=>ZZ/101)
///

doc ///
    Key
        [linkRepHomology, Homogenize]
    Headline
        Option to determine whether the group coefficient is homogeneous
    Usage
        lst =  linkRepHomology(L, matrixSize, Homogenize=>B)
    Inputs
        L : Link
        matrixSize : ZZ
        B : Boolean
    Outputs
        lst : List
    Description
        Text
            When the group type is Borel or unipotent, the group coefficient could be set homogeneous. This is the option to set whether the group coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the group is homogeneous.
        Example
            linkRepHomology(Trefoil, 3, GroupType=>"U", Homogenize=>true)
///

doc ///
    Key
        [linkRepHomologyComplex, Homogenize]
    Headline
        Option to determine whether the group coefficient is homogeneous
    Usage
        C =  linkRepHomologyComplex(L, matrixSize, Homogenize=>B)
    Inputs
        L : Link
        matrixSize : ZZ
        B : Boolean
    Outputs
        C : Complex
    Description
        Text
            When the group type is Borel or unipotent, the group coefficient could be set homogeneous. This is the option to set whether the group coefficient is homogeneous, i.e. whether the ideal to cut out the variety given by the group is homogeneous.
        Example
            linkRepHomologyComplex(Trefoil, 3, GroupType=>"U", Homogenize=>true)
///

TEST ///
-- test0 type Link
-- debug needsPackage "RepHomology"
L = link(2, {1,1,1})
assert(braidIndex(L) == braidIndex(Trefoil))
assert(word(L) == word(Trefoil))
L = link(3,{1,-2,1,-2})
assert(braidIndex(L) == braidIndex(FigureEight))
assert(word(L) == word(FigureEight))
///

TEST ///
-- test1 unipotent matrices for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(5,1, GroupType=>"Unipotent")
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

(M1, M2) = makeMatricesGroup(5, 1, CoefficientRing => ZZ/101, GroupType => "U", Homogenize => true )
assert isHomogeneous ideal(M1#0 * M2#0 * inverse(M1#0) * inverse(M2#0))
///

TEST ///
-- test2 borel matrices for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(4,1, GroupType=>"Borel")
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 4)
assert(numrows M1#0 == 4)
assert(numcols M2#0 == 4)
assert(numrows M2#0 == 4)
assert(ring M1#0 === ring M2#0)
use ring M1#0
assert(M1#0 == matrix {
            {x_(1,1,1), x_(1,1,2), x_(1,1,3), x_(1,1,4)},
            {0, x_(1,2,2), x_(1,2,3), x_(1,2,4)},
            {0, 0, x_(1,3,3), x_(1,3,4)},
            {0, 0, 0, x_(1,4,4)}})

(M1, M2) = makeMatricesGroup(4, 1, CoefficientRing => ZZ/101, GroupType => "B", Homogenize => true )
assert isHomogeneous ideal(M1#0 * M2#0 * inverse(M1#0) * inverse(M2#0))
///

TEST ///
-- test3 SL matrices for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(2,1, GroupType=>"SL")
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 2)
assert(numrows M1#0 == 2)
assert(numcols M2#0 == 2)
assert(numrows M2#0 == 2)
assert(ring M1#0 === ring M2#0)
use ring M1#0
assert(M1#0 == matrix {
            {x_(1,1,1), x_(1,1,2)},
            {x_(1,2,1), x_(1,2,2)}})
assert(det(M1#0)==1)
///

TEST ///
-- test4 GL matrices for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(2,1, GroupType=>"GL")
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 2)
assert(numrows M1#0 == 2)
assert(numcols M2#0 == 2)
assert(numrows M2#0 == 2)
assert(ring M1#0 === ring M2#0)
use ring M1#0
assert(M1#0 == matrix {
            {x_(1,1,1), x_(1,1,2)},
            {x_(1,2,1), x_(1,2,2)}})
assert(det(M1#0)!=0)
///

TEST ///
-- test5 nilpotent matrices for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(5,1, AlgType=>"nilpotent")
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 5)
assert(numrows M1#0 == 5)
assert(numcols M2#0 == 5)
assert(numrows M2#0 == 5)
assert(ring M1#0 === ring M2#0)
assert(M1#0 == matrix {
            {0, x_(1,1,2), x_(1,1,3), x_(1,1,4), x_(1,1,5)},
            {0, 0, x_(1,2,3), x_(1,2,4), x_(1,2,5)},
            {0, 0, 0, x_(1,3,4), x_(1,3,5)},
            {0, 0, 0, 0, x_(1,4,5)},
            {0, 0, 0, 0, 0}})

(M1, M2) = makeMatricesAlg(5, 1, CoefficientRing => ZZ/101, AlgType => "n", Homogenize => true )
assert isHomogeneous ideal(M1#0 * M2#0 - M2#0 * M1#0)
///

TEST ///
-- test6 borel matrices for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(4,1, AlgType=>"borel")
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 4)
assert(numrows M1#0 == 4)
assert(numcols M2#0 == 4)
assert(numrows M2#0 == 4)
assert(ring M1#0 === ring M2#0)
use ring M1#0
assert(M1#0 == matrix {
            {x_(1,1,1), x_(1,1,2), x_(1,1,3), x_(1,1,4)},
            {0, x_(1,2,2), x_(1,2,3), x_(1,2,4)},
            {0, 0, x_(1,3,3), x_(1,3,4)},
            {0, 0, 0, x_(1,4,4)}})

(M1, M2) = makeMatricesAlg(4, 1, CoefficientRing => QQ, AlgType => "b", Homogenize => true )
assert isHomogeneous ideal(M1#0 * M2#0 - M2#0 * M1#0)
///

TEST ///
-- test7 sl matrices for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(2,1, AlgType=>"sl")
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 2)
assert(numrows M1#0 == 2)
assert(numcols M2#0 == 2)
assert(numrows M2#0 == 2)
assert(ring M1#0 === ring M2#0)
use ring M1#0
assert(M1#0 == matrix {
            {x_(1,1,1), x_(1,1,2)},
            {x_(1,2,1), x_(1,2,2)}})
assert(trace(M1#0)==0)
///

TEST ///
-- test8 gl matrices for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(2,1, AlgType=>"gl")
assert(#M1 == 1)
assert(#M2 == 1)
assert(numcols M1#0 == 2)
assert(numrows M1#0 == 2)
assert(numcols M2#0 == 2)
assert(numrows M2#0 == 2)
assert(ring M1#0 === ring M2#0)
use ring M1#0
assert(M1#0 == matrix {
            {x_(1,1,1), x_(1,1,2)},
            {x_(1,2,1), x_(1,2,2)}})
///

TEST ///
-- test9 unipotent surface complex for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(4,1, GroupType=>"Unipotent")
M = M1_0 * M2_0 * inverse(M1_0) * inverse(M2_0);
C = surfaceRepHomologyChainGroup(M, 4, 1, GroupType=>"Unipotent")
assert (length C == 6)
assert (ring C === ring M1_0)
assert (dim HH_4(C) == -1)
assert (dim HH_0(C) == 9)
///

TEST ///
-- test10 borel surface complex for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(3,1, GroupType=>"Borel")
M = M1_0 * M2_0 * inverse(M1_0) * inverse(M2_0);
C = surfaceRepHomologyChainGroup(M, 3, 1, GroupType=>"Borel")
assert (length C == 6)
assert (ring C === ring M1_0)
assert (dim HH_4(C) == -1)
assert (dim HH_0(C) == 9)
///

TEST ///
-- test11 SL surface complex for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(2,1, GroupType=>"SL")
M = M1_0 * M2_0 * inverse(M1_0) * inverse(M2_0);
C = surfaceRepHomologyChainGroup(M1_0, 2, 1, GroupType=>"SL")
D = surfaceRepHomologyChainGroup(M, 2, 1, GroupType=>"SL")
assert (ring C === ring M1_0)
assert (ring D === ring M1_0)
assert (dim HH_0(C) == 3)
assert (dim HH_1(C) == -1) -- make sure taking a correct resolution
assert (dim HH_0(D) == 4)
assert (dim HH_3(C) == -1)
///

TEST ///
-- test12 GL surface complex for groups
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesGroup(2,1, GroupType=>"GL")
M = M1_0 * M2_0 * inverse(M1_0) * inverse(M2_0);
C = surfaceRepHomologyChainGroup(M1_0, 2, 1, GroupType=>"GL")
D = surfaceRepHomologyChainGroup(M, 2, 1, GroupType=>"GL")
assert (ring C === ring M1_0)
assert (ring D === ring M1_0)
assert (dim HH_0(C) == 4)
assert (dim HH_1(C) == -1) -- make sure taking a correct resolution
assert (dim HH_0(D) == 6)
assert (dim HH_2(C) == -1)
///

TEST ///
-- test13 nilpotent surface complex for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(4,1, AlgType=>"nilpotent")
M = M1_0 * M2_0 - M2_0 * M1_0
C = surfaceRepHomologyChainAlg(M, 4, 1, AlgType=>"nilpotent")
assert (length C == 6)
assert (ring C === ring M1_0)
assert (dim HH_4(C) == -1)
assert (dim HH_0(C) == 9)
///

TEST ///
-- test14 borel surface complex for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(3,1, AlgType=>"borel")
M = M1_0 * M2_0 - M2_0 * M1_0
C = surfaceRepHomologyChainAlg(M, 3, 1, AlgType=>"borel")
assert (length C == 6)
assert (ring C === ring M1_0)
assert (dim HH_4(C) == -1)
assert (dim HH_0(C) == 9)
///

TEST ///
-- test15 sl surface complex for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(2,1, AlgType=>"sl")
M = M1_0 * M2_0 - M2_0 * M1_0
C = surfaceRepHomologyChainAlg(M1_0, 2, 1, AlgType=>"sl")
D = surfaceRepHomologyChainAlg(M, 2, 1, AlgType=>"sl")
assert (ring C === ring M1_0)
assert (ring D === ring M1_0)
assert (dim HH_0(C) == 3)
assert (dim HH_1(C) == -1) -- make sure taking a correct resolution
assert (dim HH_0(D) == 4)
assert (dim HH_3(C) == -1)
///

TEST ///
-- test16 gl surface complex for algebras
debug needsPackage "RepHomology"
(M1, M2) = makeMatricesAlg(2,1, AlgType=>"gl")
M = M1_0 * M2_0 - M2_0 * M1_0
C = surfaceRepHomologyChainAlg(M1_0, 2, 1, AlgType=>"gl")
D = surfaceRepHomologyChainAlg(M, 2, 1, AlgType=>"gl")
assert (ring C === ring M1_0)
assert (ring D === ring M1_0)
assert (dim HH_0(C) == 4)
assert (dim HH_1(C) == -1) -- make sure taking a correct resolution
assert (dim HH_0(D) == 6)
assert (dim HH_2(C) == -1)
///

TEST ///
-- test17 unipotent link complex for groups
debug needsPackage "RepHomology"
L = link(1,{}) -- unlink
n = 4; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"Unipotent")
C = linkRepChain(L, X, Y, n, GroupType=>"Unipotent")
assert (length C == 6)
assert (dim ring C == dim ring X_0 - 6)
assert (dim HH_7(C) == -1)
assert (dim HH_0(C) == 6)
L = Trefoil -- trefoil link
n = 3; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"Unipotent")
D = linkRepChain(L, X, Y, n, GroupType=>"Unipotent")
assert (length D == 6)
assert (dim ring D == dim ring X_0 - 6)
assert (dim HH_4(D) == -1)
assert (dim HH_0(D) == 3)
///

TEST ///
-- test18 borel link complex for groups
debug needsPackage "RepHomology"
L = link(1,{}) -- unlink
n = 3; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"Borel")
C = linkRepChain(L, X, Y, n, GroupType=>"Borel")
assert (length C == 6)
assert (dim ring C == dim ring X_0 - 6)
assert (dim HH_7(C) == -1)
assert (dim HH_0(C) == 6)
L = Trefoil -- trefoil link
n = 2; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"Borel")
D = linkRepChain(L, X, Y, n, GroupType=>"Borel")
assert (length D == 6)
assert (dim ring D == dim ring X_0 - 6)
assert (dim HH_4(D) == -1)
assert (dim HH_0(D) == 3)
///

TEST ///
-- test19 SL link complex for groups
debug needsPackage "RepHomology"
L = link(1,{}) -- unlink
n = 2; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"SL")
C = linkRepChain(L, X, Y, n, GroupType=>"SL")
assert (length C == 3)
assert (dim ring C == dim ring X_0 - 3)
assert (dim HH_4(C) == -1)
assert (dim HH_0(C) == 3)
L = Trefoil -- trefoil link
n = 2; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"SL")
D = linkRepChain(L, X, Y, n, GroupType=>"SL")
assert (length D == 6)
assert (dim ring D == dim ring X_0 - 6)
--assert (dim HH_2(D) == -1)--need a more approachable test
assert (dim HH_0(D) == 4)
///

TEST ///
-- test20 GL link complex for groups
debug needsPackage "RepHomology"
L = link(1,{}) -- unlink
n = 2; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"GL")
C = linkRepChain(L, X, Y, n, GroupType=>"GL")
assert (length C == 4)
assert (dim ring C == dim ring X_0 - 4)
assert (dim HH_5(C) == -1)
assert (dim HH_0(C) == 4)
L = Trefoil -- trefoil link
n = 2; -- n by n matrices
(X, Y) = makeMatricesGroup(n, braidIndex(L), GroupType=>"GL")
D = linkRepChain(L, X, Y, n, GroupType=>"GL")
assert (length D == 8)
assert (dim ring D == dim ring X_0 - 8)
--assert (dim HH_2(D) == -1)--need a more approachable test
assert (dim HH_0(D) == 5)
///

end--

restart
uninstallPackage "RepHomology"
installPackage "RepHomology"
check "RepHomology"
viewHelp RepHomology