module Naming where

existential = '^'

cExists str  = exists str

clExists str = exists str

exists str   = last str == existential

mkExists str = str ++ [existential]

