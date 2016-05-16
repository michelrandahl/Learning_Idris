module Main

import Data.Vect

Position : Type
Position = (Double, Double)

--tri : Vect 3 Position
--tri = [(0.0, 0.0), (3.0,0.0), (0.0, 4.0)]

Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0.0, 0.0), (3.0,0.0), (0.0, 4.0)]

StringOrInt : Bool -> Type
StringOrInt False = String
StringOrInt True = Int

getStringOrInt : (isInt: Bool) -> StringOrInt isInt
getStringOrInt False = "ninety four"
getStringOrInt True = 94

valToString : (isInt: Bool) -> (case isInt of
                                    False => String
                                    True => Int) -> String
valToString False x = trim x
valToString True x = cast x

AdderType : (numargs: Nat) -> Type -> Type
AdderType Z numType = numType
AdderType (S k) numType = (next: numType) -> AdderType k numType

adder : Num numType => (numargs: Nat) -> numType -> AdderType numargs numType
adder Z acc = acc
adder (S k) acc = \next => adder k (next + acc)

intAdder : Int -> Int -> Int -> Int
intAdder = adder 2

data Format = Number Format
            | Str Format
            | Chr Format
            | Dble Format
            | Lit String Format -- any other literal
            | End

PrintfType : Format -> Type
PrintfType (Number fmt) = (i: Int) -> PrintfType fmt
PrintfType (Str fmt) = (str: String) -> PrintfType fmt
PrintfType (Chr fmt) = (c: Char) -> PrintfType fmt
PrintfType (Dble fmt) = (d: Double) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printFmt : (fmt: Format) -> (acc: String) -> PrintfType fmt
printFmt (Number fmt) acc = \i => printFmt fmt (acc ++ show i)
printFmt (Str fmt) acc = \str => printFmt fmt (acc ++ str)
printFmt (Chr fmt) acc = \c => printFmt fmt (acc ++ show c)
printFmt (Dble fmt) acc = \d => printFmt fmt (acc ++ show d)
printFmt (Lit lit fmt) acc = printFmt fmt (acc ++ lit)
printFmt End acc = acc

toFormat : (xs: List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dble (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) =
  case toFormat chars of
       Lit lit chars' => Lit (strCons c lit) chars'
       fmt            => Lit (strCons c "") fmt

printf : (fmt: String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printFmt _ ""

test_string : String
test_string = printf "%s: %d = %d" "this is true" 42 42


-- 6.2.3 Exercises
Matrix : (n: Nat) -> (m: Nat) -> Type
Matrix n m = Vect n (Vect m Double)

TupleVect : Nat -> Type -> Type
TupleVect Z x = ()
TupleVect (S k) x = (x, TupleVect k x)

test_tuple_vect : TupleVect 4 Nat
test_tuple_vect = (1, 2, 3, 4, ())






