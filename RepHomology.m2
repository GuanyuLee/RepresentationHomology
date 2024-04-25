-*
   Copyright 2024, -.
*-

newPackage(
    "RepHomology",
    Version => "0.2",
    Date => ", 2024",
    Authors => {
	{Name => "Guanyu Li", Email => "gl479@cornell.edu", HomePage => "https://sites.google.com/view/guanyu-li-math/home"}},
    Headline => "-",
    Keywords => {"Documentation"},
    AuxiliaryFiles => false,
    PackageExports => {"Complexes"},
    DebuggingMode => false
    )

export { -- methods
    "SurfaceRepHomologyGroup",
    "SurfaceRepHomologyLie",
    "makeMatricesLie", -- only for a test
    -- types
    "GroupType",
    "LieType",
    "Homogenize"
    }

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
    else if (opts.GroupType == "U") or (opts.GroupType == "Unipotent") then ( -- Unipotent groups
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

RepHomologyChainGroup = method (Options => {
        GroupType => "GL"
        })
RepHomologyChainGroup(Matrix, ZZ, ZZ) := ChainComplex => opts -> (M, matrixSize, genusOfSurface) -> (
    n := matrixSize;
    g := genusOfSurface;
    if opts.GroupType == "GL" then (
        return koszul matrix {flatten for i from 0 to n-1 list
            for j from 0 to n-1 list if i==j then M_(i,j)-1 else M_(i,j)};
    )
    else if opts.GroupType == "SL" then(
    )
    else if (opts.GroupType == "U") or (opts.GroupType == "Unipotent") then (
        return koszul matrix {flatten for i from 0 to n-1 list
            for j from i+1 to n-1 list M_(i,j)};
    )
    else if (opts.GroupType == "B") or (opts.GroupType == "Borel") then (
        return koszul matrix {flatten for i from 0 to n-1 list
            for j from i to n-1 list if i==j then M_(i,j)-1 else M_(i,j)};
    ) else error "The group type is not supported.";
)

-*
print the homology group of a Koszul complex

Warning : the function is valid for non-Koszul complexes, however it stops when the first time the homology is 0
*-
printKoszulHH = method ()
printKoszulHH(ChainComplex) := C -> (
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
SurfaceRepHomologyGroup = method (Options => options makeMatricesGroup)
SurfaceRepHomologyGroup(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    -- construct the matrices
    (X, Y) := makeMatricesGroup(n, g, CoefficientRing => opts.CoefficientRing, GroupType => opts.GroupType, Variables => opts.Variables);

    -- the matrix for the complex
    M := product for k from 0 to g-1 list (X_k * Y_k * inverse(X_k) * inverse(Y_k));

    -- construct the koszul complex
    C := RepHomologyChainGroup(M, n, g, GroupType => opts.GroupType);

    -- print the result
    printKoszulHH(C)
)

----------------------------------------------------
--Lie algebra version of representation homology of surfaces
----------------------------------------------------

makeMatricesLie = method (Options => {
        Homogenize => false,
        CoefficientRing => QQ,
        LieType => "gl",
        Variables => {getSymbol "x", getSymbol "y"}
        })
makeMatricesLie(ZZ, ZZ) := (List, List) => opts -> (matrixSize, genus) -> (
    n := matrixSize;
    g := genus;
    variables := opts.Variables;
    local XX; local YY; local XDeg; local YDeg; local S; local T; local SDeg; local TDeg; local R; local X; local Y; local M; local N; local I; local Xnew; local Ynew;
    if opts.LieType == "gl" then (
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
    else if opts.LieType == "sl" then (
    )
    else if (opts.LieType == "n") or (opts.LieType == "nilpotent") then (
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
    ) else if (opts.LieType == "b") or (opts.LieType == "borel") then (
    ) else error "The Lie algebra type is not supported.";
    (Xnew, Ynew)
)

RepHomologyChainLie = method (Options => {
        LieType => "gl"
        })
RepHomologyChainLie(Matrix, ZZ, ZZ) := ChainComplex => opts -> (M, matrixSize, genusOfSurface) -> (
    n := matrixSize;
    g := genusOfSurface;
    if opts.LieType == "gl" then (
    )
    else if (opts.LieType == "n") or (opts.LieType == "nilpotent") then (
        return koszul matrix {flatten for i from 0 to n-1 list
            for j from i+1 to n-1 list M_(i,j)};
    )
    else if (opts.LieType == "b") or (opts.LieType == "borel") then (
    ) else error "The group type is not supported.";
)

SurfaceRepHomologyLie = method (Options => options makeMatricesLie)
SurfaceRepHomologyLie(ZZ, ZZ) := opts -> (matrixSize, genusOfSurface) -> (
    n := matrixSize; g := genusOfSurface;
    -- construct the matrices
    (X, Y) := makeMatricesLie(n, g, CoefficientRing => opts.CoefficientRing, LieType => opts.LieType, Variables => opts.Variables);

    -- the matrix for the complex
    M := sum for k from 0 to g-1 list (X_k * Y_k - Y_k * X_k);

    -- construct the koszul complex
    C := RepHomologyChainLie(M, n, g, LieType => opts.LieType);

    -- print the result
    printKoszulHH(C)
)

----------------------------------------------------
--Representation homology of links
----------------------------------------------------

beginDocumentation()

///
 Node
  Key
   FirstPackage
  Headline
     an example Macaulay2 package
  Description
   Text
    {\em FirstPackage} is a basic package to be used as an example.
  Caveat
    Still trying to figure this out.
  Subnodes
    firstFunction
 Node
  Key
   (firstFunction,ZZ)
   firstFunction
  Headline
   a silly first function
  Usage
   firstFunction n
  Inputs
   n:
  Outputs
   :
    a silly string, depending on the value of {\tt n}
  Description
   Text
    Here we show an example.
   Example
    firstFunction 1
    firstFunction 0
///

TEST ///
(M1, M2) = makeGroupMatrices(kk, "Unipotent", {x,y,s,t}, {5,1})
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

(M1, M2) = makeGroupMatrices(5, 1, CoefficientRing => QQ, Group => "U", Homogenize => true )
assert isHomogeneous ideal(M1#0 * M2#0 - M2#0 * M1#0)
///

end--
