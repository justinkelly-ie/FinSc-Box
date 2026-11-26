module FinScBox.MultisetCodec

import Data.DPair
import Data.List
import Data.Nat
import Decidable.Equality
import FinScBox.BoxInt
import FinScBox.Interfaces
import FinScBox.Box
import FinScBox.HereditaryMSet

%default total

--------------------------------------------------------------------------------
-- 1. TOTAL BASE-10 INTEGER RENDERING (DIRECT `Integer`, ZERO PEANO `Nat`!)
--------------------------------------------------------------------------------

||| Renders a single base-10 integer digit (`0..9`) directly to its ASCII `Char`.
public export
digitIntToChar : Integer -> Char
digitIntToChar 0 = '0'
digitIntToChar 1 = '1'
digitIntToChar 2 = '2'
digitIntToChar 3 = '3'
digitIntToChar 4 = '4'
digitIntToChar 5 = '5'
digitIntToChar 6 = '6'
digitIntToChar 7 = '7'
digitIntToChar 8 = '8'
digitIntToChar 9 = '9'
digitIntToChar _ = '?'

||| Total O(log10 N) formatting directly on non-negative `Integer` via `divModIntegerPos`.
public export
posIntToCharsFuel : Nat -> Integer -> List Char -> List Char
posIntToCharsFuel Z     _ acc = acc
posIntToCharsFuel (S f) n acc =
  if n < 10
    then digitIntToChar n :: acc
    else let (q, r) = divModIntegerPos n 10
         in posIntToCharsFuel f q (digitIntToChar r :: acc)

||| Renders an `Integer` in base 10 matching `Show Integer`.
public export
renderInteger : Integer -> String
renderInteger n =
  if n == 0
    then "0"
    else if n < 0
      then pack ('-' :: posIntToCharsFuel maxBitScanFuel (-n) [])
      else pack (posIntToCharsFuel maxBitScanFuel n [])

--------------------------------------------------------------------------------
-- 2. CANONICAL MULTISET RENDERER (EXACT PARITY WITH `FinScBox.HereditaryMSet.show`)
--------------------------------------------------------------------------------

mutual
  ||| Renders a list of `(PureMultiset, BoxInt)` entries inside `{...}`.
  public export
  renderPureEntries : Nat -> List (PureMultiset, BoxInt) -> String
  renderPureEntries _ [] = ""
  renderPureEntries rem [(k, w)] =
    renderPureFuel rem k ++ ":[" ++ renderInteger (unwrapBox w) ++ "]"
  renderPureEntries rem ((k, w) :: rest) =
    renderPureFuel rem k ++ ":[" ++ renderInteger (unwrapBox w) ++ "], " ++ renderPureEntries rem rest

  ||| Renders a `PureMultiset` recursively bounded by fuel `rem`.
  public export
  renderPureFuel : Nat -> PureMultiset -> String
  renderPureFuel _ (MkHMSet BoxLeaf) = "[]"
  renderPureFuel Z _                 = "[...]"
  renderPureFuel (S rem) (MkHMSet b) =
    "{" ++ renderPureEntries rem (toAscListBox b) ++ "}"

||| Canonical total renderer producing identical text to `FinScBox.HereditaryMSet.show`.
public export
renderPureMultiset : PureMultiset -> String
renderPureMultiset m = renderPureFuel (hmDepth m) m

--------------------------------------------------------------------------------
-- 3. TOTAL FUELED PARSER OVER `List Char`
--------------------------------------------------------------------------------

||| Parses a single ASCII digit `0..9` directly to `Integer`.
public export
charToDigitInt : Char -> Maybe Integer
charToDigitInt '0' = Just 0
charToDigitInt '1' = Just 1
charToDigitInt '2' = Just 2
charToDigitInt '3' = Just 3
charToDigitInt '4' = Just 4
charToDigitInt '5' = Just 5
charToDigitInt '6' = Just 6
charToDigitInt '7' = Just 7
charToDigitInt '8' = Just 8
charToDigitInt '9' = Just 9
charToDigitInt _   = Nothing

public export
skipSpaces : List Char -> List Char
skipSpaces (' ' :: cs) = skipSpaces cs
skipSpaces cs          = cs

public export
parseDigitsAcc : Nat -> Integer -> Bool -> List Char -> Maybe (Integer, List Char)
parseDigitsAcc Z     acc hasDig cs = if hasDig then Just (acc, cs) else Nothing
parseDigitsAcc (S f) acc hasDig [] = if hasDig then Just (acc, []) else Nothing
parseDigitsAcc (S f) acc hasDig (c :: cs) =
  case charToDigitInt c of
    Just d  => parseDigitsAcc f (acc * 10 + d) True cs
    Nothing => if hasDig then Just (acc, c :: cs) else Nothing

public export
parseSignedInteger : Nat -> List Char -> Maybe (Integer, List Char)
parseSignedInteger fuel ('-' :: cs) =
  case parseDigitsAcc fuel 0 False cs of
    Just (mag, rest) => Just (-mag, rest)
    Nothing          => Nothing
parseSignedInteger fuel cs = parseDigitsAcc fuel 0 False cs

public export
parseBracketWeight : Nat -> List Char -> Maybe (BoxInt, List Char)
parseBracketWeight fuel ('[' :: cs) =
  case parseSignedInteger fuel (skipSpaces cs) of
    Just (v, rest1) =>
      case skipSpaces rest1 of
        (']' :: rest2) => Just (MkBoxInt v, rest2)
        _               => Nothing
    Nothing => Nothing
parseBracketWeight _ _ = Nothing

mutual
  public export
  parseEntriesFuel : Nat -> PureMultiset -> List Char -> Maybe (PureMultiset, List Char)
  parseEntriesFuel Z _ _ = Nothing
  parseEntriesFuel (S fuel) acc cs =
    case skipSpaces cs of
      ('}' :: rest) => Just (acc, rest)
      other =>
        case parseMSetFuel fuel other of
          Just (keyM, rest1) =>
            case skipSpaces rest1 of
              (':' :: rest2) =>
                case parseBracketWeight fuel (skipSpaces rest2) of
                  Just (w, rest3) =>
                    let (MkHMSet boxAcc) = acc
                        nextAcc = MkHMSet (addAtKeyBox keyM w boxAcc)
                    in case skipSpaces rest3 of
                         (',' :: more) => parseEntriesFuel fuel nextAcc more
                         ('}' :: rest4) => Just (nextAcc, rest4)
                         _ => Nothing
                  Nothing => Nothing
              _ => Nothing
          Nothing => Nothing

  public export
  parseMSetFuel : Nat -> List Char -> Maybe (PureMultiset, List Char)
  parseMSetFuel Z _ = Nothing
  parseMSetFuel (S fuel) cs =
    case skipSpaces cs of
      ('[' :: rest) =>
        case skipSpaces rest of
          (']' :: more) => Just (emptyHMSet, more)
          _             => Nothing
      ('{' :: rest) =>
        case skipSpaces rest of
          ('}' :: more) => Just (emptyHMSet, more)
          other         => parseEntriesFuel fuel emptyHMSet other
      _ => Nothing

||| Parses canonical `Show` / `renderPureMultiset` text into a `PureMultiset`.
||| All keys are consolidated via `addAtKeyBox` so AVL ordering and zero-pruning are enforced.
public export
parsePureMultiset : String -> Maybe PureMultiset
parsePureMultiset s =
  let chars = unpack s
  in case parseMSetFuel (S (length chars)) chars of
       Just (m, rest) =>
         case skipSpaces rest of
           [] => Just m
           _  => Nothing
       Nothing => Nothing

--------------------------------------------------------------------------------
-- 4. CONSTRUCTIVIST `Dec` RECOGNIZER (`recognition-rule.md`)
--------------------------------------------------------------------------------

public export
isValidPureMultisetText : String -> Bool
isValidPureMultisetText s =
  case parsePureMultiset s of
    Just _  => True
    Nothing => False

||| Total constructivist `Dec` recognizer certifying a serialized string parses cleanly.
public export
recognizePureMultisetText : (s : String) -> Dec (isValidPureMultisetText s = True)
recognizePureMultisetText s = decideBoolTrue (isValidPureMultisetText s)

||| Decodes serialized multiset text and certifies recursive AVL canonical invariants.
public export
decodeCanonicalMultiset : (s : String) -> Maybe (Subset PureMultiset (\m => isCanonicalHMSet m = True))
decodeCanonicalMultiset s =
  case parsePureMultiset s of
    Nothing => Nothing
    Just m  => toCanonicalHMSet m

--------------------------------------------------------------------------------
-- 5. COMPILE-TIME QTT 0 CODEC ROUND-TRIP PROOFS
--------------------------------------------------------------------------------

public export
0 prfRenderEmpty :
  FinScBox.MultisetCodec.renderPureMultiset FinScBox.HereditaryMSet.emptyHMSet = "[]"
prfRenderEmpty = Refl

public export
0 prfCodecRoundTripVacuum :
  (case FinScBox.MultisetCodec.parsePureMultiset
          (FinScBox.MultisetCodec.renderPureMultiset FinScBox.HereditaryMSet.emptyHMSet) of
     Just m  => m == FinScBox.HereditaryMSet.emptyHMSet
     Nothing => False) = True
prfCodecRoundTripVacuum = Refl

public export
0 prfCodecRoundTripBlack1 :
  (let b1 = FinScBox.HereditaryMSet.scalarKeyHMSet 1
   in case FinScBox.MultisetCodec.parsePureMultiset
             (FinScBox.MultisetCodec.renderPureMultiset b1) of
        Just m  => m == b1
        Nothing => False) = True
prfCodecRoundTripBlack1 = Refl

public export
0 prfCodecRoundTripNeg1 :
  (let r1 = FinScBox.HereditaryMSet.scalarKeyHMSet (-1)
   in case FinScBox.MultisetCodec.parsePureMultiset
             (FinScBox.MultisetCodec.renderPureMultiset r1) of
        Just m  => m == r1
        Nothing => False) = True
prfCodecRoundTripNeg1 = Refl
