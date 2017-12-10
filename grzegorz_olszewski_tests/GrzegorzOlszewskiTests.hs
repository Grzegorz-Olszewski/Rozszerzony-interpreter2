-- Wymagamy, by moduł zawierał tylko bezpieczne funkcje
{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający testy.
-- Należy zmienić nazwę modułu na {Imie}{Nazwisko}Tests gdzie za {Imie}
-- i {Nazwisko} należy podstawić odpowiednio swoje imię i nazwisko
-- zaczynające się wielką literą oraz bez znaków diakrytycznych.
module GrzegorzOlszewskiTests(tests) where

-- Importujemy moduł zawierający typy danych potrzebne w zadaniu
import DataTypes

-- Lista testów do zadania
-- Należy uzupełnić jej definicję swoimi testami
tests :: [Test]
tests =
  [ Test "unused_wrong_function" (SrcString "fun fun1(x:int):int = true in fun1(5)") TypeError,
    Test "map_and_sum" (SrcFile "test1.pp6") (Eval [] (Value 10)) ,
    Test "summing_nested_lists" (SrcFile "test2.pp6") (Eval [1,2,3] (Value 9)),
    Test "half"(SrcString "input x in if x mod 2 = 0 then let fun1 = fn (z:int)-> z div 2 in fun1(x) else let fun2 = fn (y:int) -> (x+1) div 2 in fun2(x)") (Eval [3] (Value 2)),
    Test "nested"(SrcFile "test3.pp6") (Eval [0] (Value 6)),
    Test "scalar_product"(SrcFile "test4.pp6") (Eval [1,2,3,4] (Value 11)),
    Test "factorial" (SrcFile "test5.pp6") (Eval [4] (Value 24)),
    Test "to_nth_power"(SrcFile "test6.pp6") (Eval[3,4] (Value 81)),
    Test "function_dividing_by_zero"(SrcFile "test7.pp6") (Eval [] RuntimeError)
  ]
