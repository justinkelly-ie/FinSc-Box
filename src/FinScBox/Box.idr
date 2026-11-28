module FinScBox.Box

import Data.List
import public Data.DPair
import public Data.Maybe
import public FinScBox.BoxInt
import public FinScBox.Interfaces

%default total

------------------------------------------------------------------------
-- 1. CANONICAL HEIGHT-CACHED AVL BOX CONTAINER (`Box c k`)
------------------------------------------------------------------------

||| Canonical coordinate-indexed multiset carrier (`Box c k`) backed by an
||| O(log N) height-cached AVL binary search tree mapping keys `k` to
||| multiplicity weights `c` (typically `BoxInt`, `SignedBit`, or `MultisetBit`).
public export
data Box : (c : Type) -> (k : Type) -> Type where
  BoxLeaf : Box c k
  BoxNode : (height : Nat) -> (left : Box c k) -> (key : k) -> (weight : c) -> (right : Box c k) -> Box c k

||| O(1) cached AVL height accessor.
public export
boxHeight : Box c k -> Nat
boxHeight BoxLeaf              = Z
boxHeight (BoxNode h _ _ _ _)  = h

||| Exact structural node count (non-zero entry bound) for `GohBound` and zipper termination.
public export
boxNodeCount : Box c k -> Nat
boxNodeCount BoxLeaf             = Z
boxNodeCount (BoxNode _ l _ _ r) = S (boxNodeCount l + boxNodeCount r)

||| Construct an AVL node recomputing cached height in O(1).
public export
mkBoxNode : Box c k -> k -> c -> Box c k -> Box c k
mkBoxNode l k w r =
  let hl = boxHeight l
      hr = boxHeight r
  in BoxNode (S (if hl >= hr then hl else hr)) l k w r

------------------------------------------------------------------------
-- 2. AVL ROTATIONS, BALANCING & DELETION
------------------------------------------------------------------------

||| Single right rotation preserving in-order key ordering.
public export
rotateRightBox : Box c k -> k -> c -> Box c k -> Box c k
rotateRightBox (BoxNode _ ll lx lc lr) x c r = mkBoxNode ll lx lc (mkBoxNode lr x c r)
rotateRightBox l                       x c r = mkBoxNode l x c r

||| Single left rotation preserving in-order key ordering.
public export
rotateLeftBox : Box c k -> k -> c -> Box c k -> Box c k
rotateLeftBox l x c (BoxNode _ rl rx rc rr) = mkBoxNode (mkBoxNode l x c rl) rx rc rr
rotateLeftBox l x c r                       = mkBoxNode l x c r

||| AVL height-rebalancing constructor.
public export
balanceBoxNode : Box c k -> k -> c -> Box c k -> Box c k
balanceBoxNode l x c r =
  let hl = boxHeight l
      hr = boxHeight r
  in if hl > hr + 1 then
       case l of
         BoxLeaf => mkBoxNode l x c r
         BoxNode _ ll lx lc lr =>
           if boxHeight ll >= boxHeight lr
             then rotateRightBox l x c r
             else rotateRightBox (rotateLeftBox ll lx lc lr) x c r
     else if hr > hl + 1 then
       case r of
         BoxLeaf => mkBoxNode l x c r
         BoxNode _ rl rx rc rr =>
           if boxHeight rr >= boxHeight rl
             then rotateLeftBox l x c r
             else rotateLeftBox l x c (rotateRightBox rl rx rc rr)
     else
       mkBoxNode l x c r

||| Extracts and removes the minimum-key entry of a non-empty `Box c k`.
public export
extractMinBox : Box c k -> Maybe (k, c, Box c k)
extractMinBox BoxLeaf = Nothing
extractMinBox (BoxNode _ BoxLeaf x c r) = Just (x, c, r)
extractMinBox (BoxNode _ l x c r) =
  case extractMinBox l of
    Nothing => Just (x, c, r)
    Just (minK, minW, l') => Just (minK, minW, balanceBoxNode l' x c r)

||| Deletes the root entry given left and right subtrees, rebalancing in O(log N).
public export
deleteRootBoxNode : Box c k -> k -> Box c k -> Box c k
deleteRootBoxNode BoxLeaf _ r = r
deleteRootBoxNode l       _ BoxLeaf = l
deleteRootBoxNode l       _ r =
  case extractMinBox r of
    Nothing => l
    Just (minK, minW, r') => balanceBoxNode l minK minW r'

||| Joins AVL trees `l` and `r` with root `(k, w)` when `boxHeight l > boxHeight r + 1`.
public export
joinRightBox : Box c k -> k -> c -> Box c k -> Box c k
joinRightBox BoxLeaf k w r = mkBoxNode BoxLeaf k w r
joinRightBox l@(BoxNode hl ll lx lw lr) k w r =
  if hl <= boxHeight r + 1
    then balanceBoxNode l k w r
    else balanceBoxNode ll lx lw (joinRightBox lr k w r)

||| Joins AVL trees `l` and `r` with root `(k, w)` when `boxHeight r > boxHeight l + 1`.
public export
joinLeftBox : Box c k -> k -> c -> Box c k -> Box c k
joinLeftBox l k w BoxLeaf = mkBoxNode l k w BoxLeaf
joinLeftBox l k w r@(BoxNode hr rl rx rw rr) =
  if hr <= boxHeight l + 1
    then balanceBoxNode l k w r
    else balanceBoxNode (joinLeftBox l k w rl) rx rw rr

||| General O(|hL - hR|) AVL join preserving strict BST ordering (`l < k < r`) with zero key comparisons.
public export
joinBox : Box c k -> k -> c -> Box c k -> Box c k
joinBox l k w r =
  if boxHeight l > boxHeight r + 1
    then joinRightBox l k w r
    else if boxHeight r > boxHeight l + 1
      then joinLeftBox l k w r
      else mkBoxNode l k w r

||| Joins two disjoint ordered AVL trees (`keys l < keys r`) with zero key comparisons.
public export
join2Box : Box c k -> Box c k -> Box c k
join2Box BoxLeaf r = r
join2Box l BoxLeaf = l
join2Box l r =
  case extractMinBox r of
    Nothing               => l
    Just (minK, minW, r') => joinBox l minK minW r'

||| Splits `Box c k` around key `x` into `(< x, lookup x, > x)` in O(log N).
public export
splitBox : Ord k => k -> Box c k -> (Box c k, Maybe c, Box c k)
splitBox _ BoxLeaf = (BoxLeaf, Nothing, BoxLeaf)
splitBox x (BoxNode _ l k w r) =
  case compare x k of
    EQ => (l, Just w, r)
    LT => let (ll, found, lr) = splitBox x l
          in (ll, found, joinBox lr k w r)
    GT => let (rl, found, rr) = splitBox x r
          in (joinBox l k w rl, found, rr)

||| Deletes a key from `Box c k` while preserving AVL balance.
public export
deleteBox : Ord k => k -> Box c k -> Box c k
deleteBox _ BoxLeaf = BoxLeaf
deleteBox target (BoxNode _ l k w r) =
  case compare target k of
    LT => balanceBoxNode (deleteBox target l) k w r
    GT => balanceBoxNode l k w (deleteBox target r)
    EQ => deleteRootBoxNode l k r

------------------------------------------------------------------------
-- 3. KEYED LOOKUPS, OVERWRITES & ACCUMULATING INSERTIONS
------------------------------------------------------------------------

||| Looks up a key in `Box c k`, returning `zeroWeight` when absent.
public export
lookupBox : Ord k => MultisetWeight c => k -> Box c k -> c
lookupBox _   BoxLeaf = zeroWeight
lookupBox val (BoxNode _ l x w r) =
  case compare val x of
    EQ => w
    LT => lookupBox val l
    GT => lookupBox val r

||| Canonical zero-pruning overwrite: sets `val` to `w`, deleting the node
||| whenever `isZero w` holds so `BoxLeaf` remains the unique canonical zero.
public export
setBox : Ord k => MultisetWeight c => k -> c -> Box c k -> Box c k
setBox val w BoxLeaf =
  if isZero w then BoxLeaf else BoxNode 1 BoxLeaf val w BoxLeaf
setBox val w (BoxNode _ l x cur r) =
  case compare val x of
    EQ => if isZero w then deleteRootBoxNode l x r else mkBoxNode l x w r
    LT => balanceBoxNode (setBox val w l) x cur r
    GT => balanceBoxNode l x cur (setBox val w r)

||| Accumulates `dw` onto `val` (`cur + dw`), pruning on annihilation.
public export
addAtKeyBox : Ord k => MultisetWeight c => k -> c -> Box c k -> Box c k
addAtKeyBox val dw BoxLeaf =
  if isZero dw then BoxLeaf else BoxNode 1 BoxLeaf val dw BoxLeaf
addAtKeyBox val dw node@(BoxNode _ l x cur r) =
  if isZero dw then node
  else case compare val x of
         EQ => let newW = addWeight cur dw
               in if isZero newW then deleteRootBoxNode l x r else mkBoxNode l x newW r
         LT => balanceBoxNode (addAtKeyBox val dw l) x cur r
         GT => balanceBoxNode l x cur (addAtKeyBox val dw r)

||| Direct lexicographic pair comparison avoiding per-call `Ord (a, b)` dictionary allocation.
public export
comparePairDirect : Ord a => Ord b => a -> b -> (a, b) -> Ordering
comparePairDirect x y (kx, ky) =
  case compare x kx of
    EQ  => compare y ky
    ord => ord

||| Zero-tuple-allocation lookup on `Box c (a, b)` avoiding `Ord (a, b)` dictionary construction.
public export
lookupPairBox : Ord a => Ord b => MultisetWeight c => a -> b -> Box c (a, b) -> c
lookupPairBox _ _ BoxLeaf = zeroWeight
lookupPairBox x y (BoxNode _ l k w r) =
  case comparePairDirect x y k of
    EQ => w
    LT => lookupPairBox x y l
    GT => lookupPairBox x y r

||| Zero-dictionary-allocation overwrite on `Box c (a, b)`, reusing existing key pair on updates.
public export
setPairBox : Ord a => Ord b => MultisetWeight c => a -> b -> c -> Box c (a, b) -> Box c (a, b)
setPairBox x y w BoxLeaf =
  if isZero w then BoxLeaf else BoxNode 1 BoxLeaf (x, y) w BoxLeaf
setPairBox x y w (BoxNode _ l k cur r) =
  case comparePairDirect x y k of
    EQ => if isZero w then deleteRootBoxNode l k r else mkBoxNode l k w r
    LT => balanceBoxNode (setPairBox x y w l) k cur r
    GT => balanceBoxNode l k cur (setPairBox x y w r)

||| Zero-dictionary-allocation accumulation on `Box c (a, b)`, reusing existing key pair on updates.
public export
addAtPairBox : Ord a => Ord b => MultisetWeight c => a -> b -> c -> Box c (a, b) -> Box c (a, b)
addAtPairBox x y dw BoxLeaf =
  if isZero dw then BoxLeaf else BoxNode 1 BoxLeaf (x, y) dw BoxLeaf
addAtPairBox x y dw node@(BoxNode _ l k cur r) =
  if isZero dw then node
  else case comparePairDirect x y k of
         EQ => let newW = addWeight cur dw
               in if isZero newW then deleteRootBoxNode l k r else mkBoxNode l k newW r
         LT => balanceBoxNode (addAtPairBox x y dw l) k cur r
         GT => balanceBoxNode l k cur (addAtPairBox x y dw r)

------------------------------------------------------------------------
-- 4. CONSTRUCTORS & IN-ORDER FOLDING
------------------------------------------------------------------------

||| Constructs a zero-pruned singleton `Box c k`.
public export
singletonBox : MultisetWeight c => k -> c -> Box c k
singletonBox k w = if isZero w then BoxLeaf else BoxNode 1 BoxLeaf k w BoxLeaf

||| In-order left fold `(k -> c -> acc -> acc)` over `Box c k`.
public export
foldBox : (k -> c -> acc -> acc) -> acc -> Box c k -> acc
foldBox _ acc BoxLeaf = acc
foldBox f acc (BoxNode _ l k w r) =
  let accL = foldBox f acc l
      accM = f k w accL
  in foldBox f accM r

||| Structurally recursive in-order right fold `(k -> c -> b -> b)` over `Box c k`.
public export
foldBoxTreeR : (f : k -> c -> b -> b) -> b -> Box c k -> b
foldBoxTreeR _ z BoxLeaf = z
foldBoxTreeR f z (BoxNode _ l k w r) =
  foldBoxTreeR f (f k w (foldBoxTreeR f z r)) l

||| O(N) difference-list right-to-left accumulator materializing sorted pairs.
public export
toAscListBoxAcc : Box c k -> List (k, c) -> List (k, c)
toAscListBoxAcc BoxLeaf acc = acc
toAscListBoxAcc (BoxNode _ l k w r) acc =
  toAscListBoxAcc l ((k, w) :: toAscListBoxAcc r acc)

||| Extracts ascending `(key, weight)` pairs from a `Box c k` in O(N).
public export
toAscListBox : Box c k -> List (k, c)
toAscListBox box = toAscListBoxAcc box []

||| Maps a function over weights in `Box c k`, preserving AVL structure.
public export
mapBoxWeight : (c -> d) -> Box c k -> Box d k
mapBoxWeight _ BoxLeaf = BoxLeaf
mapBoxWeight f (BoxNode h l k w r) = BoxNode h (mapBoxWeight f l) k (f w) (mapBoxWeight f r)

||| Evaluates the number of active non-zero weight nodes in a `Box c k` with zero heap allocation.
public export
treeSizeNonZero : MultisetWeight c => Box c k -> Nat
treeSizeNonZero = foldBox (\_, w, acc => if isZero w then acc else S acc) 0

||| Short-circuiting universal predicate over all stored `(key, weight)` entries in `Box c k`.
public export
allBox : (k -> c -> Bool) -> Box c k -> Bool
allBox _ BoxLeaf             = True
allBox p (BoxNode _ l k w r) = p k w && allBox p l && allBox p r

||| Short-circuiting in-order search returning the first `Just` result in `Box c k`.
public export
findBox : (k -> c -> Maybe r) -> Box c k -> Maybe r
findBox _ BoxLeaf = Nothing
findBox f (BoxNode _ l k w r) =
  case findBox f l of
    Just res => Just res
    Nothing  =>
      case f k w of
        Just res => Just res
        Nothing  => findBox f r

||| Maps a weight function over `Box c k` and prunes any resulting `zeroWeight` entries in O(N) with zero key comparisons.
public export
mapPruneBox : MultisetWeight d => (c -> d) -> Box c k -> Box d k
mapPruneBox _ BoxLeaf = BoxLeaf
mapPruneBox f (BoxNode _ l k w r) =
  let l' = mapPruneBox f l
      r' = mapPruneBox f r
      w' = f w
  in if isZero w' then join2Box l' r' else joinBox l' k w' r'

------------------------------------------------------------------------
-- 5. BOUNDED LEFT-SPINE ZIPPER, EQUALITY & ORDERING (ZERO LIST ALLOCATION)
------------------------------------------------------------------------

||| Incremental AVL left-spine traversal zipper avoiding full-tree `List` allocation.
public export
BoxZipper : (c : Type) -> (k : Type) -> Type
BoxZipper c k = List (k, c, Box c k)

||| Pushes the left spine of a `Box c k` onto an existing zipper stack.
public export
pushLeftBox : Box c k -> BoxZipper c k -> BoxZipper c k
pushLeftBox BoxLeaf acc = acc
pushLeftBox (BoxNode _ l k w r) acc = pushLeftBox l ((k, w, r) :: acc)

||| Pops the next active non-zero entry from a `BoxZipper c k`, bounded by remaining node count.
public export
popNextNonZeroZipper : MultisetWeight c => Nat -> BoxZipper c k -> Maybe (k, c, BoxZipper c k)
popNextNonZeroZipper Z _ = Nothing
popNextNonZeroZipper (S fuel) stk =
  case stk of
    [] => Nothing
    ((k, w, r) :: rest) =>
      let nextStk = pushLeftBox r rest
      in if isZero w then popNextNonZeroZipper fuel nextStk else Just (k, w, nextStk)

||| Bounded probe pop distinguishing clean exhaustion (`Just Nothing`) from probe fuel exhaustion (`Nothing`).
public export
popNextNonZeroZipperTry : MultisetWeight c => Nat -> BoxZipper c k -> Maybe (Maybe (k, c, BoxZipper c k))
popNextNonZeroZipperTry _ [] = Just Nothing
popNextNonZeroZipperTry Z _  = Nothing
popNextNonZeroZipperTry (S fuel) ((k, w, r) :: rest) =
  let nextStk = pushLeftBox r rest
  in if isZero w then popNextNonZeroZipperTry fuel nextStk else Just (Just (k, w, nextStk))

||| Fueled left-spine comparison on non-zero entries of two `Box c k` trees.
public export
compareBoxZipperFuel : Ord k => MultisetWeight c =>
                       Nat -> BoxZipper c k -> BoxZipper c k -> Ordering
compareBoxZipperFuel Z _ _ = EQ
compareBoxZipperFuel (S fuel) z1 z2 =
  case (popNextNonZeroZipper (S fuel) z1, popNextNonZeroZipper (S fuel) z2) of
    (Nothing, Nothing) => EQ
    (Nothing, Just _)  => LT
    (Just _,  Nothing) => GT
    (Just (k1, w1, r1), Just (k2, w2, r2)) =>
      case compare k1 k2 of
        EQ => case compare w1 w2 of
                EQ  => compareBoxZipperFuel fuel r1 r2
                ord => ord
        ord => ord

||| Zero-pre-scan probe comparator returning `Just ord` when decided within `fuel` steps,
||| avoiding `boxNodeCount` scans on early mismatches and small trees.
public export
compareBoxZipperTry : Ord k => MultisetWeight c =>
                      Nat -> BoxZipper c k -> BoxZipper c k -> Maybe Ordering
compareBoxZipperTry Z _ _ = Nothing
compareBoxZipperTry (S fuel) z1 z2 =
  case (popNextNonZeroZipperTry (S fuel) z1, popNextNonZeroZipperTry (S fuel) z2) of
    (Just Nothing, Just Nothing)   => Just EQ
    (Just Nothing, Just (Just _))  => Just LT
    (Just (Just _), Just Nothing)  => Just GT
    (Just (Just (k1, w1, r1)), Just (Just (k2, w2, r2))) =>
      case compare k1 k2 of
        EQ => case compare w1 w2 of
                EQ  => compareBoxZipperTry fuel r1 r2
                ord => Just ord
        ord => Just ord
    _ => Nothing

||| Zero-allocation fast path checking equality when two `Box c k` trees share identical AVL shape.
public export
sameShapeBoxEqual : Eq k => MultisetWeight c => Box c k -> Box c k -> Bool
sameShapeBoxEqual BoxLeaf BoxLeaf = True
sameShapeBoxEqual (BoxNode h1 l1 k1 w1 r1) (BoxNode h2 l2 k2 w2 r2) =
  h1 == h2 && k1 == k2 && w1 == w2 && sameShapeBoxEqual l1 l2 && sameShapeBoxEqual r1 r2
sameShapeBoxEqual _ _ = False

public export
eqBoxZipperTry : Eq k => MultisetWeight c => Nat -> BoxZipper c k -> BoxZipper c k -> Maybe Bool
eqBoxZipperTry Z _ _ = Nothing
eqBoxZipperTry (S fuel) z1 z2 =
  case (popNextNonZeroZipperTry (S fuel) z1, popNextNonZeroZipperTry (S fuel) z2) of
    (Just Nothing, Just Nothing)  => Just True
    (Just Nothing, Just (Just _)) => Just False
    (Just (Just _), Just Nothing) => Just False
    (Just (Just (k1, w1, r1)), Just (Just (k2, w2, r2))) =>
      if k1 == k2 && w1 == w2 then eqBoxZipperTry fuel r1 r2 else Just False
    _ => Nothing

||| Structural equality test via zero-allocation same-shape check, bounded O(1) probe,
||| and full incremental non-zero zipper fallback.
public export
structuralBoxTreeEqual : Eq k => MultisetWeight c => Box c k -> Box c k -> Bool
structuralBoxTreeEqual t1 t2 =
  if sameShapeBoxEqual t1 t2
    then True
    else
      let z1 = pushLeftBox t1 []
          z2 = pushLeftBox t2 []
      in case eqBoxZipperTry 16 z1 z2 of
           Just res => res
           Nothing  => go (S (boxNodeCount t1 + boxNodeCount t2)) z1 z2
  where
    go : Nat -> BoxZipper c k -> BoxZipper c k -> Bool
    go Z _ _ = True
    go (S fuel) z1 z2 =
      case (popNextNonZeroZipper (S fuel) z1, popNextNonZeroZipper (S fuel) z2) of
        (Nothing, Nothing) => True
        (Just (k1, w1, r1), Just (k2, w2, r2)) =>
          (k1 == k2) && (w1 == w2) && go fuel r1 r2
        _ => False

public export
Eq k => MultisetWeight c => Eq (Box c k) where
  (==) = structuralBoxTreeEqual

public export
Ord k => MultisetWeight c => Ord (Box c k) where
  compare t1 t2 =
    let z1 = pushLeftBox t1 []
        z2 = pushLeftBox t2 []
    in case compareBoxZipperTry 16 z1 z2 of
         Just ord => ord
         Nothing  => compareBoxZipperFuel (S (boxNodeCount t1 + boxNodeCount t2)) z1 z2

public export
Show k => Show c => Show (Box c k) where
  show t = "Box(" ++ show (toAscListBox t) ++ ")"

public export
Foldable (Box c) where
  foldr f z t = foldBoxTreeR (\x, _, acc => f x acc) z t

------------------------------------------------------------------------
-- 6. POINTWISE ALGEBRAIC, RELATIONAL & PAIRWISE PRODUCT OPERATORS
------------------------------------------------------------------------

||| Pointwise negation of all weights in a `Box c k`.
public export
negateBox : MultisetWeight c => Box c k -> Box c k
negateBox = mapBoxWeight negWeight

||| Tree-to-tree AVL split/join union (`O(M log(N/M + 1))`, zero `List` allocation).
public export
unionSplitBox : Ord k => MultisetWeight c => Box c k -> Box c k -> Box c k
unionSplitBox BoxLeaf t2 = t2
unionSplitBox t1 BoxLeaf = t1
unionSplitBox (BoxNode _ l1 k w1 r1) t2 =
  let (l2, optW2, r2) = splitBox k t2
      l' = unionSplitBox l1 l2
      r' = unionSplitBox r1 r2
  in case optW2 of
       Nothing => joinBox l' k w1 r'
       Just w2 =>
         let w' = addWeight w1 w2
         in if isZero w' then join2Box l' r' else joinBox l' k w' r'

||| Exact pointwise superposition/sum of two `Box c k` structures (`A + B`), pruning zeros.
public export
unionBox : Ord k => MultisetWeight c => Box c k -> Box c k -> Box c k
unionBox BoxLeaf t2 = t2
unionBox t1 BoxLeaf = t1
unionBox t1 t2 =
  let h1 = boxHeight t1
      h2 = boxHeight t2
  in if h1 > h2 + 2
       then foldBox (\k, w, acc => addAtKeyBox k w acc) t1 t2
       else if h2 > h1 + 2
         then foldBox (\k, w, acc => addAtKeyBox k w acc) t2 t1
         else unionSplitBox t1 t2

||| Tree-to-tree AVL split/join difference (`A - B`, zero `List` allocation).
public export
subSplitBox : Ord k => MultisetWeight c => Box c k -> Box c k -> Box c k
subSplitBox BoxLeaf t2 = negateBox t2
subSplitBox t1 BoxLeaf = t1
subSplitBox (BoxNode _ l1 k w1 r1) t2 =
  let (l2, optW2, r2) = splitBox k t2
      l' = subSplitBox l1 l2
      r' = subSplitBox r1 r2
  in case optW2 of
       Nothing => joinBox l' k w1 r'
       Just w2 =>
         let w' = addWeight w1 (negWeight w2)
         in if isZero w' then join2Box l' r' else joinBox l' k w' r'

||| Pointwise difference of two `Box c k` structures (`A - B`), pruning zeros.
public export
subBox : Ord k => MultisetWeight c => Box c k -> Box c k -> Box c k
subBox BoxLeaf t2 = negateBox t2
subBox t1 BoxLeaf = t1
subBox t1 t2 =
  if boxHeight t1 > boxHeight t2 + 2
    then foldBox (\k, w, acc => addAtKeyBox k (negWeight w) acc) t1 t2
    else subSplitBox t1 t2

||| Pointwise scalar multiplication by `s : c`, annihilating immediately when `isZero s` (no `Ord k` needed).
public export
scaleBox : MultisetWeight c => c -> Box c k -> Box c k
scaleBox s t =
  if isZero s then BoxLeaf else mapBoxWeight (mulWeight s) t

||| Total signed weight (`sum_k w_k`) across all active coordinates.
public export
totalMassBox : MultisetWeight c => Box c k -> c
totalMassBox = foldBox (\_, w, acc => addWeight acc w) zeroWeight

||| Filters entries of `Box c k` by a key predicate in O(N) with zero key comparisons.
public export
filterBox : (k -> Bool) -> Box c k -> Box c k
filterBox _ BoxLeaf = BoxLeaf
filterBox p (BoxNode _ l k w r) =
  let l' = filterBox p l
      r' = filterBox p r
  in if p k then joinBox l' k w r' else join2Box l' r'

||| Unsigned support indicator (`oneWeight {c=d}` on every non-zero key, `zeroWeight` pruned) in O(N).
public export
supportBox : MultisetWeight c => MultisetWeight d => Box c k -> Box d k
supportBox = mapPruneBox (\w => if isZero w then zeroWeight else oneWeight)

||| Single-pass O(N) partition of `Box c k` into `(matching, nonMatching)` with zero key comparisons.
public export
partitionBox : (k -> Bool) -> Box c k -> (Box c k, Box c k)
partitionBox _ BoxLeaf = (BoxLeaf, BoxLeaf)
partitionBox p (BoxNode _ l k w r) =
  let (ly, ln) = partitionBox p l
      (ry, rn) = partitionBox p r
  in if p k
       then (joinBox ly k w ry, join2Box ln rn)
       else (join2Box ly ry, joinBox ln k w rn)

||| Retains entries of `t` whose keys are non-zero in `mask`, folding over the smaller-height tree.
public export
maskByBox : Ord k => MultisetWeight c => MultisetWeight d => Box c k -> Box d k -> Box c k
maskByBox BoxLeaf _ = BoxLeaf
maskByBox _ BoxLeaf = BoxLeaf
maskByBox t mask =
  if boxHeight t <= boxHeight mask
    then filterBox (\k => not (isZero (lookupBox k mask))) t
    else foldBox (\k, mw, acc => if isZero mw then acc else setBox k (lookupBox k t) acc) BoxLeaf mask

||| Retains entries of `t` whose keys are zero (absent) in `mask`.
public export
maskOutBox : Ord k => MultisetWeight c => MultisetWeight d => Box d k -> Box c k -> Box c k
maskOutBox BoxLeaf t = t
maskOutBox _ BoxLeaf = BoxLeaf
maskOutBox mask t = filterBox (\k => isZero (lookupBox k mask)) t

||| Tree-to-tree AVL split/join Hadamard product (`O(M log(N/M + 1))`, preserving operand order).
public export
hadamardSplitBox : Ord k => MultisetWeight c => Bool -> Box c k -> Box c k -> Box c k
hadamardSplitBox _ BoxLeaf _ = BoxLeaf
hadamardSplitBox _ _ BoxLeaf = BoxLeaf
hadamardSplitBox flipMul (BoxNode _ l1 k w1 r1) t2 =
  let (l2, optW2, r2) = splitBox k t2
      l' = hadamardSplitBox flipMul l1 l2
      r' = hadamardSplitBox flipMul r1 r2
  in case optW2 of
       Nothing => join2Box l' r'
       Just w2 =>
         let prod = if flipMul then mulWeight w2 w1 else mulWeight w1 w2
         in if isZero prod then join2Box l' r' else joinBox l' k prod r'

||| Pointwise Hadamard product (`A .*. B`) on `Box c k`, using split/join for comparable trees
||| and smaller-tree lookup for tiny masks while preserving `mulWeight w1 w2` operand order.
public export
hadamardBox : Ord k => MultisetWeight c => Box c k -> Box c k -> Box c k
hadamardBox BoxLeaf _ = BoxLeaf
hadamardBox _ BoxLeaf = BoxLeaf
hadamardBox t1 t2 =
  let h1 = boxHeight t1
      h2 = boxHeight t2
  in if h1 <= h2
       then if h1 <= 2
              then foldBox (\k, w1, acc =>
                              let prod = mulWeight w1 (lookupBox k t2)
                              in if isZero prod then acc else setBox k prod acc)
                           BoxLeaf t1
              else hadamardSplitBox False t1 t2
       else if h2 <= 2
              then foldBox (\k, w2, acc =>
                              let prod = mulWeight (lookupBox k t1) w2
                              in if isZero prod then acc else setBox k prod acc)
                           BoxLeaf t2
              else hadamardSplitBox True t2 t1

||| Canonical inner product (`A <.> B`) returning scalar multiplicity weight `c`,
||| folding over the smaller-height tree while preserving `mulWeight w1 w2` operand order.
public export
dotBox : Ord k => MultisetWeight c => Box c k -> Box c k -> c
dotBox BoxLeaf _ = zeroWeight
dotBox _ BoxLeaf = zeroWeight
dotBox t1 t2 =
  if boxHeight t1 <= boxHeight t2
    then foldBox (\k, w1, acc => addWeight acc (mulWeight w1 (lookupBox k t2))) zeroWeight t1
    else foldBox (\k, w2, acc => addWeight acc (mulWeight (lookupBox k t1) w2)) zeroWeight t2

||| Generalized all-pairs box multiplication (`pairBoxWith`):
||| Pairs every active `(k1, w1)` in `t1` with every active `(k2, w2)` in `t2`,
||| combines coordinates via `f k1 k2`, multiplies weights via `mulWeight w1 w2`,
||| and consolidates colliding output keys with automatic zero-pruning.
public export
pairBoxWith : Ord k3 => MultisetWeight c =>
              (f : k1 -> k2 -> k3) ->
              Box c k1 ->
              Box c k2 ->
              Box c k3
pairBoxWith _ BoxLeaf _ = BoxLeaf
pairBoxWith _ _ BoxLeaf = BoxLeaf
pairBoxWith f t1 t2 =
  foldBox (\k1, w1, treeAcc =>
             foldBox (\k2, w2, acc =>
                        let prod = mulWeight w1 w2
                        in if isZero prod then acc else addAtKeyBox (f k1 k2) prod acc)
                     treeAcc
                     t2)
          BoxLeaf
          t1

||| Cartesian outer product (`tensorBox`): `Box c k1 -> Box c k2 -> Box c (k1, k2)`.
public export
tensorBox : Ord k1 => Ord k2 => MultisetWeight c => Box c k1 -> Box c k2 -> Box c (k1, k2)
tensorBox = pairBoxWith (,)

||| Right index contraction / marginalization summing out `k2`.
public export
contractRBox : Ord k1 => MultisetWeight c => Box c (k1, k2) -> Box c k1
contractRBox BoxLeaf = BoxLeaf
contractRBox m = foldBox (\(c1, _), w, acc => addAtKeyBox c1 w acc) BoxLeaf m

||| Left index contraction / marginalization summing out `k1`.
public export
contractLBox : Ord k2 => MultisetWeight c => Box c (k1, k2) -> Box c k2
contractLBox BoxLeaf = BoxLeaf
contractLBox m = foldBox (\(_, c2), w, acc => addAtKeyBox c2 w acc) BoxLeaf m

||| Coordinate pushforward re-indexing `k1 -> k2` and summing colliding multiplicities.
public export
mapBox : Ord k2 => MultisetWeight c => (k1 -> k2) -> Box c k1 -> Box c k2
mapBox _ BoxLeaf = BoxLeaf
mapBox f m = foldBox (\c1, w, acc => addAtKeyBox (f c1) w acc) BoxLeaf m

||| Monoidal convolution (`mulBoxWith`) over any `MonoidCoord k` and `MultisetWeight c`.
public export
mulBoxWith : MonoidCoord k => MultisetWeight c => Box c k -> Box c k -> Box c k
mulBoxWith = pairBoxWith combine

||| Pair coordinate transposition: swaps (a, b) -> (b, a).
public export
transposeBox : Ord a => Ord b => MultisetWeight c => Box c (a, b) -> Box c (b, a)
transposeBox BoxLeaf = BoxLeaf
transposeBox m =
  foldBox (\(x, y), w, acc =>
            if isZero w then acc else addAtPairBox y x w acc)
          BoxLeaf m

public export
insertRowBucket : Ord b => b -> (c, w) -> Box (List (c, w)) b -> Box (List (c, w)) b
insertRowBucket key entry BoxLeaf = BoxNode 1 BoxLeaf key [entry] BoxLeaf
insertRowBucket key entry (BoxNode _ l k vs r) =
  case compare key k of
    EQ => mkBoxNode l k (entry :: vs) r
    LT => balanceBoxNode (insertRowBucket key entry l) k vs r
    GT => balanceBoxNode l k vs (insertRowBucket key entry r)

public export
lookupRowBucket : Ord b => b -> Box (List (c, w)) b -> List (c, w)
lookupRowBucket _ BoxLeaf = []
lookupRowBucket key (BoxNode _ l k vs r) =
  case compare key k of
    EQ => vs
    LT => lookupRowBucket key l
    GT => lookupRowBucket key r

public export
addRowBucketProducts : Ord a => Ord c => MultisetWeight w => a -> w -> List (c, w) -> Box w (a, c) -> Box w (a, c)
addRowBucketProducts _ _  []             acc = acc
addRowBucketProducts a w1 ((c, w2) :: xs) acc =
  addRowBucketProducts a w1 xs (addAtPairBox a c (mulWeight w1 w2) acc)

||| Row-indexed sparse pixel-fusion contraction: `[a, b] * [b, c] -> [a, c]` in O(|M2| log |M2| + work).
public export
composeBox : Ord a => Ord b => Ord c => MultisetWeight w =>
             Box w (a, b) -> Box w (b, c) -> Box w (a, c)
composeBox BoxLeaf _ = BoxLeaf
composeBox _ BoxLeaf = BoxLeaf
composeBox m1 m2 =
  let rows2 = foldBox (\(b2, c), w2, acc =>
                         if isZero w2 then acc else insertRowBucket b2 (c, w2) acc)
                      BoxLeaf m2
  in foldBox (\(a, b1), w1, acc =>
                if isZero w1
                  then acc
                  else addRowBucketProducts a w1 (lookupRowBucket b1 rows2) acc)
             BoxLeaf m1

||| Trace of a square 2D multiset: sums multiplicities on the diagonal a1 == a2.
public export
traceBox : Eq a => MultisetWeight c => Box c (a, a) -> c
traceBox BoxLeaf = zeroWeight
traceBox m =
  foldBox (\(x, y), w, acc =>
            if x == y then addWeight acc w else acc)
          zeroWeight m

||| Diagonal embedding of a 1D `Box c k` onto the coincidence diagonal `(k, k)` in O(N) with zero key comparisons.
public export
diagEmbedBox : MultisetWeight c => Box c k -> Box c (k, k)
diagEmbedBox BoxLeaf = BoxLeaf
diagEmbedBox (BoxNode h l k w r) = BoxNode h (diagEmbedBox l) (k, k) w (diagEmbedBox r)

||| Symmetry form index of a 2-parameter Wildberger `Maxel`, type-bound to `(a, b)`:
||| - `GeneralForm`     : arbitrary rectangular `(a, b)` or unstructured square `(k, k)`
||| - `SymForm`         : symmetric square `(k, k)` (`M[b, a] = +M[a, b]`), half-stored on `a <= b`
||| - `AntisymForm`     : antisymmetric square `(k, k)` (`M[b, a] = -M[a, b]`, `M[a, a] = 0`), half-stored on `a < b`
||| - `DiagAntisymForm` : free diagonal `M[a, a]` + antisymmetric off-diagonal (`M[b, a] = -M[a, b]`), half-stored on `a <= b`
public export
data MaxelForm : (a : Type) -> (b : Type) -> Type where
  GeneralForm     : MaxelForm a b
  SymForm         : MaxelForm k k
  AntisymForm     : MaxelForm k k
  DiagAntisymForm : MaxelForm k k

||| Form index after transposing rows and columns.
public export
transposeMaxelForm : MaxelForm a b -> MaxelForm b a
transposeMaxelForm GeneralForm     = GeneralForm
transposeMaxelForm SymForm         = SymForm
transposeMaxelForm AntisymForm     = AntisymForm
transposeMaxelForm DiagAntisymForm = DiagAntisymForm

public export
eqMaxelForm : {0 a, b, c, d : Type} -> MaxelForm a b -> MaxelForm c d -> Bool
eqMaxelForm GeneralForm     GeneralForm     = True
eqMaxelForm SymForm         SymForm         = True
eqMaxelForm AntisymForm     AntisymForm     = True
eqMaxelForm DiagAntisymForm DiagAntisymForm = True
eqMaxelForm _               _               = False

public export
Eq (MaxelForm a b) where
  (==) = eqMaxelForm

public export
Show (MaxelForm a b) where
  show GeneralForm     = "GeneralForm"
  show SymForm         = "SymForm"
  show AntisymForm     = "AntisymForm"
  show DiagAntisymForm = "DiagAntisymForm"

||| Runtime singleton witness for `MaxelForm`, enabling single-instance algebraic dispatch.
public export
data MaxelFormTag : MaxelForm a b -> Type where
  TagGeneral     : MaxelFormTag GeneralForm
  TagSym         : MaxelFormTag SymForm
  TagAntisym     : MaxelFormTag AntisymForm
  TagDiagAntisym : MaxelFormTag DiagAntisymForm

public export
Eq (MaxelFormTag form) where
  _ == _ = True

public export
Show (MaxelFormTag form) where
  show TagGeneral     = "TagGeneral"
  show TagSym         = "TagSym"
  show TagAntisym     = "TagAntisym"
  show TagDiagAntisym = "TagDiagAntisym"

public export
interface KnownMaxelForm (0 form : MaxelForm a b) where
  maxelFormTag : MaxelFormTag form

public export
KnownMaxelForm GeneralForm where
  maxelFormTag = TagGeneral

public export
KnownMaxelForm SymForm where
  maxelFormTag = TagSym

public export
KnownMaxelForm AntisymForm where
  maxelFormTag = TagAntisym

public export
KnownMaxelForm DiagAntisymForm where
  maxelFormTag = TagDiagAntisym

||| Canonical Wildberger 2-index Maxel `sum w_{ab} [a, b]` type-bound to `(a, b)`.
||| Uses canonical half-storage (`a <= b` / `a < b`) and O(1) structural symmetries when `a = b`.
public export
record Maxel (c : Type) (a : Type) (b : Type) (form : MaxelForm a b) where
  constructor MkMaxel
  rawMaxelBox : Box c (a, b)

public export
(Eq a, Eq b, MultisetWeight c) => Eq (Maxel c a b form) where
  m1 == m2 = m1.rawMaxelBox == m2.rawMaxelBox

public export
(Ord a, Ord b, MultisetWeight c) => Ord (Maxel c a b form) where
  compare m1 m2 = compare m1.rawMaxelBox m2.rawMaxelBox

public export
(Show a, Show b, Show c) => Show (Maxel c a b form) where
  show m = "Maxel(" ++ show (toAscListBox m.rawMaxelBox) ++ ")"

public export
emptyMaxel : Maxel c a b form
emptyMaxel = MkMaxel BoxLeaf

public export
isEmptyMaxel : Maxel c a b form -> Bool
isEmptyMaxel (MkMaxel BoxLeaf) = True
isEmptyMaxel _                 = False

public export
maxelNodeCount : MultisetWeight c => Maxel c a b form -> Nat
maxelNodeCount m = treeSizeNonZero m.rawMaxelBox

||| Sums all canonically stored multiplicities in `Maxel c a b form`.
public export
sumStoredMaxel : MultisetWeight c => Maxel c a b form -> c
sumStoredMaxel (MkMaxel m) = totalMassBox m

||| Folds over the canonically stored `(a, b, w)` entries of `Maxel c a b form`.
public export
foldStoredMaxel : (a -> b -> c -> acc -> acc) -> acc -> Maxel c a b form -> acc
foldStoredMaxel f acc (MkMaxel m) = foldBox (\(x, y), w, a => f x y w a) acc m

||| Filters canonically stored entries of `Maxel c a b form` by an index-pair predicate in O(N).
public export
filterMaxel : (a -> b -> Bool) -> Maxel c a b form -> Maxel c a b form
filterMaxel p (MkMaxel m) = MkMaxel (filterBox (\(x, y) => p x y) m)

||| Zeroes the coincidence diagonal `(x, x)` while preserving `form` in O(N).
public export
offDiagMaxel : Eq k => Maxel c k k form -> Maxel c k k form
offDiagMaxel = filterMaxel (/=)

||| Maps a weight function over stored entries of `Maxel c a b form`, pruning zeros in O(N).
public export
mapPruneMaxel : MultisetWeight d => (c -> d) -> Maxel c a b form -> Maxel d a b form
mapPruneMaxel f (MkMaxel m) = MkMaxel (mapPruneBox f m)

||| Retains stored entries of `Maxel c a b form` whose canonical keys are active in `mask`.
public export
maskByMaxel : Ord a => Ord b => MultisetWeight c => MultisetWeight d =>
              Maxel c a b form -> Maxel d a b form -> Maxel c a b form
maskByMaxel (MkMaxel m) (MkMaxel mask) = MkMaxel (maskByBox m mask)

||| Right index contraction summing out `b` from a `GeneralForm` Maxel.
public export
contractRMaxel : Ord a => MultisetWeight c => Maxel c a b GeneralForm -> Box c a
contractRMaxel (MkMaxel m) = contractRBox m

||| Left index contraction summing out `a` from a `GeneralForm` Maxel.
public export
contractLMaxel : Ord b => MultisetWeight c => Maxel c a b GeneralForm -> Box c b
contractLMaxel (MkMaxel m) = contractLBox m

||| Relational / matrix composition `[a, b1] * [b2, d] -> [a, d]` (`b1 == b2`) on `GeneralForm` Maxels.
public export
composeMaxel : Ord a => Ord b => Ord d => MultisetWeight c =>
               Maxel c a b GeneralForm -> Maxel c b d GeneralForm -> Maxel c a d GeneralForm
composeMaxel (MkMaxel m1) (MkMaxel m2) = MkMaxel (composeBox m1 m2)

||| Right linear action `(M v)_a = sum_b M[a, b] * v[b]` of a `GeneralForm` Maxel on `Box c b`.
public export
actMaxelR : Ord a => Ord b => MultisetWeight c => Maxel c a b GeneralForm -> Box c b -> Box c a
actMaxelR (MkMaxel m) v =
  foldBox (\(x, y), w, acc => addAtKeyBox x (mulWeight w (lookupBox y v)) acc) BoxLeaf m

public export
lookupHalfBox : Ord k => MultisetWeight c => (allowDiag, antisymOff : Bool) -> k -> k -> Box c (k, k) -> c
lookupHalfBox allowDiag antisymOff x y m =
  case compare x y of
    LT => lookupPairBox x y m
    EQ => if allowDiag then lookupPairBox x x m else zeroWeight
    GT => let w = lookupPairBox y x m in if antisymOff then negWeight w else w

public export
updateHalfBox :
  Ord k => MultisetWeight c =>
  (isAdd, allowDiag, antisymOff : Bool) ->
  k -> k -> c -> Box c (k, k) -> Box c (k, k)
updateHalfBox isAdd allowDiag antisymOff x y w m =
  if isAdd && isZero w
    then m
    else case compare x y of
           LT => if isAdd then addAtPairBox x y w m else setPairBox x y w m
           EQ => if allowDiag then (if isAdd then addAtPairBox x x w m else setPairBox x x w m) else m
           GT => if isAdd
                   then addAtPairBox y x (if antisymOff then negWeight w else w) m
                   else setPairBox   y x (if antisymOff then negWeight w else w) m

||| Extracts the diagonal `(x, x)` weights of any square `Maxel` into `Box c k` in O(N) with zero `Ord k` inserts.
public export
diagBox : Eq k => Maxel c k k form -> Box c k
diagBox (MkMaxel m) = go m
  where
    go : Box c (k, k) -> Box c k
    go BoxLeaf = BoxLeaf
    go (BoxNode _ l (x, y) w r) =
      let l' = go l
          r' = go r
      in if x == y then joinBox l' x w r' else join2Box l' r'

public export
lookupMaxel :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  {form : MaxelForm a b} -> a -> b -> Maxel c a b form -> c
lookupMaxel {form = GeneralForm}     x y (MkMaxel m) = lookupPairBox @{ordA} @{ordB} @{mw} x y m
lookupMaxel {form = SymForm}         x y (MkMaxel m) = lookupHalfBox @{ordA} @{mw} True  False x y m
lookupMaxel {form = AntisymForm}     x y (MkMaxel m) = lookupHalfBox @{ordA} @{mw} False True  x y m
lookupMaxel {form = DiagAntisymForm} x y (MkMaxel m) = lookupHalfBox @{ordA} @{mw} True  True  x y m

public export
setMaxelEdge :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  {form : MaxelForm a b} -> a -> b -> c -> Maxel c a b form -> Maxel c a b form
setMaxelEdge {form = GeneralForm}     x y w (MkMaxel m) = MkMaxel (setPairBox @{ordA} @{ordB} @{mw} x y w m)
setMaxelEdge {form = SymForm}         x y w (MkMaxel m) = MkMaxel (updateHalfBox @{ordA} @{mw} False True  False x y w m)
setMaxelEdge {form = AntisymForm}     x y w (MkMaxel m) = MkMaxel (updateHalfBox @{ordA} @{mw} False False True  x y w m)
setMaxelEdge {form = DiagAntisymForm} x y w (MkMaxel m) = MkMaxel (updateHalfBox @{ordA} @{mw} False True  True  x y w m)

public export
addAtMaxelEdge :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  {form : MaxelForm a b} -> a -> b -> c -> Maxel c a b form -> Maxel c a b form
addAtMaxelEdge {form = GeneralForm}     x y w (MkMaxel m) = MkMaxel (addAtPairBox @{ordA} @{ordB} @{mw} x y w m)
addAtMaxelEdge {form = SymForm}         x y w (MkMaxel m) = MkMaxel (updateHalfBox @{ordA} @{mw} True True  False x y w m)
addAtMaxelEdge {form = AntisymForm}     x y w (MkMaxel m) = MkMaxel (updateHalfBox @{ordA} @{mw} True False True  x y w m)
addAtMaxelEdge {form = DiagAntisymForm} x y w (MkMaxel m) = MkMaxel (updateHalfBox @{ordA} @{mw} True True  True  x y w m)

public export
singletonMaxelEdge :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  {form : MaxelForm a b} -> a -> b -> c -> Maxel c a b form
singletonMaxelEdge x y w = setMaxelEdge @{ordA} @{ordB} @{mw} {form} x y w emptyMaxel

public export
transposeDiagAntisymBox : Ord k => MultisetWeight c => Box c (k, k) -> Box c (k, k)
transposeDiagAntisymBox BoxLeaf = BoxLeaf
transposeDiagAntisymBox (BoxNode h l k@(x, y) w r) =
  BoxNode h (transposeDiagAntisymBox l) k (if x == y then w else negWeight w) (transposeDiagAntisymBox r)

public export
dotSymHalfBox : Ord k => MultisetWeight c => Box c (k, k) -> Box c (k, k) -> c
dotSymHalfBox BoxLeaf _ = zeroWeight
dotSymHalfBox _ BoxLeaf = zeroWeight
dotSymHalfBox m1 m2 =
  foldBox (\(x, y), w1, acc =>
             let prod = mulWeight w1 (lookupPairBox x y m2)
             in if x == y
                  then addWeight acc prod
                  else addWeight acc (addWeight prod prod))
          zeroWeight
          m1

public export
dotMaxelByTag :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  {0 form : MaxelForm a b} -> MaxelFormTag form -> Maxel c a b form -> Maxel c a b form -> c
dotMaxelByTag TagGeneral     (MkMaxel m1) (MkMaxel m2) = dotBox m1 m2
dotMaxelByTag TagSym         (MkMaxel m1) (MkMaxel m2) = dotSymHalfBox @{ordA} @{mw} m1 m2
dotMaxelByTag TagDiagAntisym (MkMaxel m1) (MkMaxel m2) = dotSymHalfBox @{ordA} @{mw} m1 m2
dotMaxelByTag TagAntisym     (MkMaxel m1) (MkMaxel m2) =
  let half = dotKK @{ordA} m1 m2
  in addWeight half half
  where
    dotKK : Ord k => Box c (k, k) -> Box c (k, k) -> c
    dotKK = dotBox

public export
transposeMaxel :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> MultisetWeight c =>
  {form : MaxelForm a b} -> Maxel c a b form -> Maxel c b a (transposeMaxelForm form)
transposeMaxel {form = GeneralForm}     (MkMaxel m) = MkMaxel (transposeBox m)
transposeMaxel {form = SymForm}         m           = m
transposeMaxel {form = AntisymForm}     (MkMaxel m) = MkMaxel (negateBox m)
transposeMaxel {form = DiagAntisymForm} (MkMaxel m) = MkMaxel (transposeDiagAntisymBox @{ordA} m)

public export
traceMaxel : Eq k => MultisetWeight c => {form : MaxelForm k k} -> Maxel c k k form -> c
traceMaxel {form = AntisymForm} _           = zeroWeight
traceMaxel                      (MkMaxel m) = traceBox m

public export
diagEmbedMaxel : MultisetWeight c => Box c k -> Maxel c k k SymForm
diagEmbedMaxel b = MkMaxel (diagEmbedBox b)

public export
expandHalfBox : Ord k => MultisetWeight c => Bool -> (c -> c) -> Box c (k, k) -> Box c (k, k)
expandHalfBox allowDiag oppFn =
  foldBox (\(x, y), w, acc =>
             if x == y
               then if allowDiag then addAtPairBox x x w acc else acc
               else addAtPairBox y x (oppFn w) (addAtPairBox x y w acc))
          BoxLeaf

public export
toGeneralMaxel : Ord k => MultisetWeight c => {form : MaxelForm k k} -> Maxel c k k form -> Maxel c k k GeneralForm
toGeneralMaxel {form = GeneralForm}     m           = m
toGeneralMaxel {form = SymForm}         (MkMaxel m) = MkMaxel (expandHalfBox True  id        m)
toGeneralMaxel {form = AntisymForm}     (MkMaxel m) = MkMaxel (expandHalfBox False negWeight m)
toGeneralMaxel {form = DiagAntisymForm} (MkMaxel m) = MkMaxel (expandHalfBox True  negWeight m)

public export
hadamardMaxelForm : MaxelForm a b -> MaxelForm a b -> MaxelForm a b
hadamardMaxelForm GeneralForm     _               = GeneralForm
hadamardMaxelForm SymForm         GeneralForm     = GeneralForm
hadamardMaxelForm AntisymForm     GeneralForm     = GeneralForm
hadamardMaxelForm DiagAntisymForm GeneralForm     = GeneralForm
hadamardMaxelForm SymForm         SymForm         = SymForm
hadamardMaxelForm AntisymForm     AntisymForm     = SymForm
hadamardMaxelForm DiagAntisymForm DiagAntisymForm = SymForm
hadamardMaxelForm AntisymForm     DiagAntisymForm = SymForm
hadamardMaxelForm DiagAntisymForm AntisymForm     = SymForm
hadamardMaxelForm SymForm         AntisymForm     = AntisymForm
hadamardMaxelForm AntisymForm     SymForm         = AntisymForm
hadamardMaxelForm SymForm         DiagAntisymForm = DiagAntisymForm
hadamardMaxelForm DiagAntisymForm SymForm         = DiagAntisymForm

public export
hadamardMaxelByTag :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  {0 f1, f2 : MaxelForm a b} ->
  MaxelFormTag f1 -> MaxelFormTag f2 ->
  Maxel c a b f1 -> Maxel c a b f2 -> Maxel c a b (hadamardMaxelForm f1 f2)
hadamardMaxelByTag t1 t2 m1 m2 = go @{ordA} @{ordB} t1 t2 m1 m2
  where
    hadKK : Ord k => Box c (k, k) -> Box c (k, k) -> Box c (k, k)
    hadKK = hadamardBox

    go : {0 x, y : Type} -> {auto ox : Ord x} -> {auto oy : Ord y} ->
         {0 g1, g2 : MaxelForm x y} ->
         MaxelFormTag g1 -> MaxelFormTag g2 ->
         Maxel c x y g1 -> Maxel c x y g2 -> Maxel c x y (hadamardMaxelForm g1 g2)
    go TagGeneral     TagGeneral     (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadamardBox x1 x2)
    go TagGeneral     TagSym         (MkMaxel x1) x2           = MkMaxel (hadKK @{ox} x1 (toGeneralMaxel @{ox} @{mw} {form = SymForm} x2).rawMaxelBox)
    go TagGeneral     TagAntisym     (MkMaxel x1) x2           = MkMaxel (hadKK @{ox} x1 (toGeneralMaxel @{ox} @{mw} {form = AntisymForm} x2).rawMaxelBox)
    go TagGeneral     TagDiagAntisym (MkMaxel x1) x2           = MkMaxel (hadKK @{ox} x1 (toGeneralMaxel @{ox} @{mw} {form = DiagAntisymForm} x2).rawMaxelBox)
    go TagSym         TagGeneral     x1           (MkMaxel x2) = MkMaxel (hadKK @{ox} (toGeneralMaxel @{ox} @{mw} {form = SymForm} x1).rawMaxelBox x2)
    go TagAntisym     TagGeneral     x1           (MkMaxel x2) = MkMaxel (hadKK @{ox} (toGeneralMaxel @{ox} @{mw} {form = AntisymForm} x1).rawMaxelBox x2)
    go TagDiagAntisym TagGeneral     x1           (MkMaxel x2) = MkMaxel (hadKK @{ox} (toGeneralMaxel @{ox} @{mw} {form = DiagAntisymForm} x1).rawMaxelBox x2)
    go TagSym         TagSym         (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagAntisym     TagAntisym     (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagDiagAntisym TagDiagAntisym (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagAntisym     TagDiagAntisym (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagDiagAntisym TagAntisym     (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagSym         TagAntisym     (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagAntisym     TagSym         (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagSym         TagDiagAntisym (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)
    go TagDiagAntisym TagSym         (MkMaxel x1) (MkMaxel x2) = MkMaxel (hadKK @{ox} x1 x2)

||| O(N) structure-preserving coordinate translation on `Box c (k, k)` when `combine _ s` preserves `Ord k`.
public export
shiftPairTreeOne : MonoidCoord k => k -> Box c (k, k) -> Box c (k, k)
shiftPairTreeOne _ BoxLeaf = BoxLeaf
shiftPairTreeOne s (BoxNode h l (x, y) w r) =
  BoxNode h (shiftPairTreeOne s l) (combine x s, combine y s) w (shiftPairTreeOne s r)

||| O(N) order-preserving coordinate translation with scalar weight multiplication and zero-pruning.
public export
shiftPairTreeMul : MonoidCoord k => MultisetWeight c => k -> c -> Box c (k, k) -> Box c (k, k)
shiftPairTreeMul _ _  BoxLeaf = BoxLeaf
shiftPairTreeMul s w2 (BoxNode _ l (x, y) w1 r) =
  let l'   = shiftPairTreeMul s w2 l
      r'   = shiftPairTreeMul s w2 r
      prod = mulWeight w1 w2
  in if isZero prod
       then join2Box l' r'
       else joinBox l' (combine x s, combine y s) prod r'

public export
shiftConvolveMaxel :
  MonoidCoord k => MultisetWeight c =>
  {form : MaxelForm k k} ->
  Maxel c k k form ->
  Box c k ->
  Maxel c k k form
shiftConvolveMaxel (MkMaxel BoxLeaf) _ = MkMaxel BoxLeaf
shiftConvolveMaxel _ BoxLeaf           = MkMaxel BoxLeaf
shiftConvolveMaxel {k} {form} (MkMaxel m) shiftBox =
  if isOrderPreserving {k}
    then MkMaxel $ foldBox (\s, w2, outer =>
                             if isZero w2
                               then outer
                               else let shifted = if w2 == oneWeight
                                                    then if s == origin then m else shiftPairTreeOne s m
                                                    else shiftPairTreeMul s w2 m
                                    in unionBox outer shifted)
                           BoxLeaf shiftBox
    else
      let stepFn : k -> k -> c -> Box c (k, k) -> Box c (k, k)
          stepFn = case form of
                     GeneralForm     => \x', y', prod, inner => if isZero prod then inner else addAtPairBox x' y' prod inner
                     SymForm         => updateHalfBox True True  False
                     AntisymForm     => updateHalfBox True False True
                     DiagAntisymForm => updateHalfBox True True  True
      in MkMaxel $ foldBox (\s, w2, outer =>
                              if w2 == oneWeight
                                then foldBox (\(x, y), w1, inner =>
                                                stepFn (combine x s) (combine y s) w1 inner)
                                             outer m
                                else foldBox (\(x, y), w1, inner =>
                                                stepFn (combine x s) (combine y s) (mulWeight w1 w2) inner)
                                             outer m)
                           BoxLeaf shiftBox

||| Symmetric unit-step stencil `sum_{a in axes} ([+stepFn a] + [-stepFn a])` over any `GroupCoord k`.
public export
unitStencilBox : GroupCoord k => MultisetWeight c => (a -> k) -> Box d a -> Box c k
unitStencilBox stepFn =
  foldBox (\axKey, _, acc =>
             let d = stepFn axKey
             in addAtKeyBox (inverse d) oneWeight (addAtKeyBox d oneWeight acc))
          BoxLeaf

||| Scales all entries of a `Box BoxInt k` by `num`, divides symmetrically by `den`,
||| and prunes magnitudes below `minCut` in a single O(N) pass.
public export
mulDivPruneBox : (num, den, minCut : BoxInt) -> Box BoxInt k -> Box BoxInt k
mulDivPruneBox num den minCut b =
  if den <= 0 || boxIsZero num
    then BoxLeaf
    else if num == 1 && den == 1
      then if minCut <= 1
             then b
             else mapPruneBox (\w => if abs w >= minCut then w else zeroWeight) b
      else if num == 1
        then mapPruneBox (\w => let q = tdivPosBox w den
                                in if abs q >= minCut then q else zeroWeight) b
        else mapPruneBox (\w => let q = tdivPosBox (num * w) den
                                in if abs q >= minCut then q else zeroWeight) b

||| Divides all entries of a `Box BoxInt k` symmetrically by `den` and prunes values below `minCut` in O(N).
public export
scaleDivPruneBox : (den, minCut : BoxInt) -> Box BoxInt k -> Box BoxInt k
scaleDivPruneBox = mulDivPruneBox 1

public export
pruneMinMaxel : BoxInt -> Maxel BoxInt a b form -> Maxel BoxInt a b form
pruneMinMaxel minCut (MkMaxel m) = MkMaxel (mulDivPruneBox 1 1 minCut m)

public export
mulDivPruneMaxel : (num, den, minCut : BoxInt) -> Maxel BoxInt a b form -> Maxel BoxInt a b form
mulDivPruneMaxel num den minCut (MkMaxel m) = MkMaxel (mulDivPruneBox num den minCut m)

public export
scaleDivPruneMaxel : (den, minCut : BoxInt) -> Maxel BoxInt a b form -> Maxel BoxInt a b form
scaleDivPruneMaxel = mulDivPruneMaxel 1

------------------------------------------------------------------------
-- 7. STANDARD ALGEBRAIC INSTANCES ON `Box c k`
------------------------------------------------------------------------

public export
Ord k => MultisetWeight c => Semigroup (Box c k) where
  (<+>) = unionBox

public export
Ord k => MultisetWeight c => Monoid (Box c k) where
  neutral = BoxLeaf

public export
Ord a => Ord b => MultisetWeight c => Semigroup (Maxel c a b form) where
  (<+>) (MkMaxel m1) (MkMaxel m2) = MkMaxel (unionBox m1 m2)

public export
Ord a => Ord b => MultisetWeight c => Monoid (Maxel c a b form) where
  neutral = emptyMaxel

public export
Ord k => MultisetWeight c => MultisetAlgebra c (Box c k) where
  zeroM  = BoxLeaf
  addM   = unionBox
  negM   = negateBox
  subM   = subBox
  scaleM = scaleBox
  dotM   = dotBox

public export
Ord k => MultisetWeight c => MultisetHadamard (Box c k) (Box c k) (Box c k) where
  (.*.) = hadamardBox

public export
Ord a => Ord b => MultisetWeight c => KnownMaxelForm form =>
MultisetAlgebra c (Maxel c a b form) where
  zeroM                          = emptyMaxel
  addM (MkMaxel m1) (MkMaxel m2) = MkMaxel (unionBox m1 m2)
  negM (MkMaxel m)               = MkMaxel (negateBox m)
  subM (MkMaxel m1) (MkMaxel m2) = MkMaxel (subBox m1 m2)
  scaleM s (MkMaxel m)           = MkMaxel (scaleBox s m)
  dotM                           = dotMaxelByTag maxelFormTag

||| Decides whether the full square expansion of `m` is symmetric (`M^T == M`).
public export
isSymMaxel : Ord k => MultisetWeight c => {form : MaxelForm k k} -> Maxel c k k form -> Bool
isSymMaxel m = let g = toGeneralMaxel m in transposeMaxel g == g

||| Decides whether the full square expansion of `m` is antisymmetric (`M^T == -M`).
public export
isAntisymMaxel : Ord k => MultisetWeight c => {form : MaxelForm k k} -> Maxel c k k form -> Bool
isAntisymMaxel m = let g = toGeneralMaxel m in transposeMaxel g == negM g

public export
Ord a => Ord b => MultisetWeight c => KnownMaxelForm f1 => KnownMaxelForm f2 =>
MultisetHadamard (Maxel c a b f1) (Maxel c a b f2) (Maxel c a b (hadamardMaxelForm f1 f2)) where
  (.*.) = hadamardMaxelByTag maxelFormTag maxelFormTag

public export
MonoidCoord k => Num (Box BoxInt k) where
  (+) = unionBox
  (*) = mulBoxWith
  fromInteger n = singletonBox origin (MkBoxInt n)

public export
MonoidCoord k => Neg (Box BoxInt k) where
  negate = negateBox
  (-) = subBox

public export
Ord k1 => Ord k2 => MultisetWeight c => MultisetOuter (Box c k1) (Box c k2) (Box c (k1, k2)) where
  (><) = tensorBox


------------------------------------------------------------------------
-- CONSTRUCTIVIST CANONICAL AVL/ZERO-PRUNING RECOGNIZER (`recognition-rule.md`)
------------------------------------------------------------------------

||| Single-pass canonical invariant checker over `Box c k`:
||| Validates:
||| 1. No zero weights (`not (isZero w)`).
||| 2. Exact cached AVL height (`h == S (max (boxHeight l) (boxHeight r))`).
||| 3. AVL balance factor (`|hL - hR| <= 1`).
||| 4. Strict BST key ordering (`maxKey(l) < k < minKey(r)`).
||| 5. Key predicate `keyOk k` holds on every active node.
||| Returns `Nothing` if invalid, `Just Nothing` for `BoxLeaf`, or
||| `Just (Just (minKey, maxKey))` for non-empty valid subtrees.
public export
checkBoxBoundsBy : MultisetWeight c => Ord k => (k -> Bool) -> Box c k -> Maybe (Maybe (k, k))
checkBoxBoundsBy _ BoxLeaf = Just Nothing
checkBoxBoundsBy keyOk (BoxNode h l k w r) =
  if isZero w || not (keyOk k) then Nothing
  else
    let hl = boxHeight l
        hr = boxHeight r
        expectedH = S (if hl >= hr then hl else hr)
    in if h /= expectedH || hl > hr + 1 || hr > hl + 1 then Nothing
       else case (checkBoxBoundsBy keyOk l, checkBoxBoundsBy keyOk r) of
              (Just optL, Just optR) =>
                let leftOk  = case optL of Nothing => True; Just (_, lMax) => lMax < k
                    rightOk = case optR of Nothing => True; Just (rMin, _) => k < rMin
                in if leftOk && rightOk
                     then Just (Just (maybe k fst optL, maybe k snd optR))
                     else Nothing
              _ => Nothing

||| Total boolean-to-`Dec` witness lift with zero runtime overhead.
public export
decideBoolTrue : (cond : Bool) -> Dec (cond = True)
decideBoolTrue True  = Yes Refl
decideBoolTrue False = No (\case Refl impossible)

||| Polymorphic Sterling `Dec` recognizer lifting any total `Bool` predicate `pred`
||| into a runtime-decidable dependent witness `Dec (pred x = True)`.
public export
recognizeBy : {0 a : Type} -> (pred : a -> Bool) -> (x : a) -> Dec (pred x = True)
recognizeBy pred x = decideBoolTrue (pred x)

||| Polymorphic smart constructor packing a verified candidate `x` into `Subset`
||| with an erased `QTT 0` proof `0 snd : pred fst = True`.
public export
toSubsetBy : {0 a : Type} -> (pred : a -> Bool) -> (x : a) -> Maybe (Subset a (\v => pred v = True))
toSubsetBy pred x =
  case recognizeBy pred x of
    Yes prf => Just (Element x prf)
    No _    => Nothing

||| Sterling recognition predicate certifying canonical AVL height, balance,
||| strict BST key ordering, zero-pruning, and key predicate `keyOk` on `Box c k`.
public export
isCanonicalBoxBy : MultisetWeight c => Ord k => (k -> Bool) -> Box c k -> Bool
isCanonicalBoxBy keyOk m = isJust (checkBoxBoundsBy keyOk m)

||| Sterling recognition predicate certifying canonical AVL invariants and zero-pruning on `Box c k`.
public export
isCanonicalBox : MultisetWeight c => Ord k => Box c k -> Bool
isCanonicalBox = isCanonicalBoxBy (\_ => True)

public export
checkPairBox :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  ((a, b) -> Bool) -> Box c (a, b) -> Bool
checkPairBox = isCanonicalBoxBy

||| Sterling recognition predicate certifying canonical AVL invariants, zero-pruning,
||| and `form` half-storage (`x <= y` on `SymForm`/`DiagAntisymForm`, `x < y` on `AntisymForm`).
public export
isCanonicalMaxel :
  {auto ordA : Ord a} -> {auto ordB : Ord b} -> {auto mw : MultisetWeight c} ->
  {form : MaxelForm a b} -> Maxel c a b form -> Bool
isCanonicalMaxel {form = GeneralForm}     (MkMaxel m) = checkPairBox @{ordA} @{ordB} @{mw} (\_ => True) m
isCanonicalMaxel {form = SymForm}         (MkMaxel m) = checkPairBox @{ordA} @{ordA} @{mw} (\(x, y) => compare @{ordA} x y /= GT) m
isCanonicalMaxel {form = AntisymForm}     (MkMaxel m) = checkPairBox @{ordA} @{ordA} @{mw} (\(x, y) => compare @{ordA} x y == LT) m
isCanonicalMaxel {form = DiagAntisymForm} (MkMaxel m) = checkPairBox @{ordA} @{ordA} @{mw} (\(x, y) => compare @{ordA} x y /= GT) m

||| Splits a signed `Box c k` into disjoint positive (`M_+`) and negative (`M_-`) channels
||| in O(N) time with zero key comparisons, preserving canonical AVL balance.
public export
splitBoxChannels : MultisetWeight c => Box c k -> (Box c k, Box c k)
splitBoxChannels BoxLeaf = (BoxLeaf, BoxLeaf)
splitBoxChannels (BoxNode _ l k w r) =
  let (lp, ln) = splitBoxChannels l
      (rp, rn) = splitBoxChannels r
  in case compare w zeroWeight of
       GT => (joinBox lp k w rp, join2Box ln rn)
       LT => (join2Box lp rp, joinBox ln k (negWeight w) rn)
       EQ => (join2Box lp rp, join2Box ln rn)

