
module CodeGen.C.Prelude where

--------------------------------------------------------------------------------

includes :: String
includes = unlines
  [ "#include <stdint.h>"
  , "#include <stdio.h>"
  , "#include <stdlib.h>"
  ]

defines :: String
defines = unlines
  [ "#define MAX(a,b) ( ((a) >= (b)) ? (a) : (b) )"
  ]

tydefs :: String
tydefs = unlines
  [ "typedef int      Unit;"
  , "typedef int      Bit;"
  , "typedef uint64_t U64;"
  , "typedef int      Nat;"
  , ""
  , "struct S_BitU64 {"
  , "  Bit _field0;"
  , "  U64 _field1;"
  , "};"
  , ""
  , "struct S_U64U64 {"
  , "  U64 _field0;"
  , "  U64 _field1;"
  , "};"
  , ""
  , "typedef struct S_BitU64 PairBitU64;"
  , "typedef struct S_U64U64 PairU64U64;"
  ]

{-
__builtin_addcll(unsigned long long x,
                 unsigned long long y,
                 unsigned long long carryin,
                 unsigned long long *carryout);
-}

primops :: String
primops = unlines
  [ ""

{-
  , "// NOTE: Apple clang version 14.0.3 on ARM generates incorrect code from"
  , "// this with optimizations enabled (it works correctly with -O0)"
  , "//"
  , "static inline PairBitU64 addCarryU64( Bit cin , U64 x , U64 y ) {"
  , "  U64 cout_u64;"
  , "  U64 z = __builtin_addcll( x , y , (U64)cin , &cout_u64 );"
  , "  Bit cout = (Bit)cout_u64;"
  , "  PairBitU64 pair  = { cout ,  z };"
  , "  return pair;"
  , "}"
  , ""
  , "static inline PairBitU64 subCarryU64( Bit cin , U64 x , U64 y ) {"
  , "  U64 cout_u64;"
  , "  U64 z = __builtin_subcll( x , y , (U64)cin , &cout_u64 );"
  , "  Bit cout = (Bit)cout_u64;"
  , "  PairBitU64 pair  = { cout ,  z };"
  , "  return pair;"
  , "}"
-}

  , "static inline PairBitU64 addCarryU64( Bit cin , U64 x , U64 y ) {"
  , "  U64 z  = x + y + cin;"
  , "  Bit cout = ( (cin) ? (z <= x) : (z < x) );"
  , "  PairBitU64 pair  = { cout ,  z };"
  , "  return pair;"
  , "}"
  , ""
  , "static inline PairBitU64 subCarryU64( Bit cin , U64 x , U64 y ) {"
  , "  U64 z  = x - y - cin;"
  , "  Bit cout = ( (cin) ? (z >= x) : (z > x) );"
  , "  PairBitU64 pair  = { cout , z };"
  , "  return pair;"
  , "}"

  , ""
  , "static inline PairU64U64 mulExtU64( U64 x , U64 y ) {"
  , "  __uint128_t z = ((__uint128_t)x) * y;"
  , "  uint64_t lo = (uint64_t) z;"
  , "  uint64_t hi = (uint64_t)(z >> 64);"
  , "  PairU64U64 pair  = { hi , lo };"
  , "  return pair;"
  , "}"
  , ""
  , "static inline PairU64U64 mulAddU64( U64 a , U64 x , U64 y ) {"
  , "  __uint128_t z = (((__uint128_t)x) * y) + a; "
  , "  uint64_t lo = (uint64_t) z;"
  , "  uint64_t hi = (uint64_t)(z >> 64);"
  , "  PairU64U64 pair  = { hi , lo };"
  , "  return pair;"
  , "}"
  , ""
  , "static inline PairBitU64 rotLeftU64(Bit cin , U64 x) {"
  , "  Bit cout = ((x>>63) != 0);"
  , "  U64 y    = (x<<1) | ((uint64_t)cin);"
  , "  PairBitU64 pair  = { cout , y };"
  , "  return pair;"
  , "}"
  , ""
  , "static inline PairBitU64 rotRightU64(Bit cin , U64 x) {"
  , "  Bit cout = ((x&1) != 0);"
  , "  U64 y    = (x>>1) | (cin ? 0x8000000000000000 : 0);"
  , "  PairBitU64 pair  = { cout , y };"
  , "  return pair;"
  , "}"
  , ""
  ]

prints :: String
prints = unlines
  [ "void print_Unit( Unit t ) { printf(\"Tt\"); }"
  , "void print_Bit ( Bit  b ) { if (b) { printf(\"True\"); } else { printf(\"False\"); } }"
  , "void print_U64 ( U64  x ) { printf(\"0x%llx\",x); }"
  , "void print_Nat ( Nat  n ) { printf(\"%d\",n); }"
  ]
  
--------------------------------------------------------------------------------

cprelude :: String
cprelude = unlines
  [ includes
  , defines
  , tydefs
  , primops
  , prints
  ]

--------------------------------------------------------------------------------
  