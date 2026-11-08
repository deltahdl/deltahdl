#include <gtest/gtest.h>

#include <cctype>
#include <string_view>
#include <vector>

#include "simulator/svdpi.h"

namespace delta {
namespace {

#define SPELL(name) #name

bool HasInterfacePrefix(std::string_view n) {
  return n.starts_with("sv") || n.starts_with("SV_");
}

bool IsFunctionOrTypeName(std::string_view n) {
  return n.size() > 2 && n[0] == 's' && n[1] == 'v' &&
         std::isupper(static_cast<unsigned char>(n[2])) &&
         n.find('_') == std::string_view::npos;
}

bool IsSymbolicConstantName(std::string_view n) { return n.starts_with("sv_"); }

bool IsMacroName(std::string_view n) {
  if (!n.starts_with("SV_")) return false;
  for (char c : n) {
    if (std::islower(static_cast<unsigned char>(c))) return false;
  }
  return true;
}

TEST(SvdpiNamingConventions, EveryInterfaceNameHasSvPrefix) {
  EXPECT_EQ(sv_x, 3);
  svLogicVecVal vec_value{};
  (void)vec_value;
  EXPECT_GT(sizeof(&svGetScope), 0u);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFFFFFFFu, 4), 0xFu);

  EXPECT_TRUE(HasInterfacePrefix(SPELL(sv_x)));
  EXPECT_TRUE(HasInterfacePrefix(SPELL(svLogicVecVal)));
  EXPECT_TRUE(HasInterfacePrefix(SPELL(svGetScope)));
  EXPECT_TRUE(HasInterfacePrefix(SPELL(SV_GET_UNSIGNED_BITS)));
}

TEST(SvdpiNamingConventions, FunctionAndTypeNamesAreSvCamelCase) {
  svBit bit_value = 0;
  svLogicVecVal logic_vec{};
  svBitVecVal bit_vec = 0;
  svScope scope = nullptr;
  (void)bit_value;
  (void)logic_vec;
  (void)bit_vec;
  (void)scope;
  EXPECT_GT(sizeof(&svGetScope), 0u);
  EXPECT_GT(sizeof(&svDpiVersion), 0u);

  EXPECT_TRUE(IsFunctionOrTypeName(SPELL(svBit)));
  EXPECT_TRUE(IsFunctionOrTypeName(SPELL(svLogicVecVal)));
  EXPECT_TRUE(IsFunctionOrTypeName(SPELL(svBitVecVal)));
  EXPECT_TRUE(IsFunctionOrTypeName(SPELL(svScope)));
  EXPECT_TRUE(IsFunctionOrTypeName(SPELL(svGetScope)));
  EXPECT_TRUE(IsFunctionOrTypeName(SPELL(svDpiVersion)));

  EXPECT_FALSE(IsSymbolicConstantName(SPELL(svLogicVecVal)));
  EXPECT_FALSE(IsMacroName(SPELL(svLogicVecVal)));
}

TEST(SvdpiNamingConventions, SymbolicConstantNamesUseSvUnderscore) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);
  EXPECT_NE(sv_scaled_real_time, sv_sim_time);

  EXPECT_TRUE(IsSymbolicConstantName(SPELL(sv_0)));
  EXPECT_TRUE(IsSymbolicConstantName(SPELL(sv_1)));
  EXPECT_TRUE(IsSymbolicConstantName(SPELL(sv_z)));
  EXPECT_TRUE(IsSymbolicConstantName(SPELL(sv_x)));
  EXPECT_TRUE(IsSymbolicConstantName(SPELL(sv_scaled_real_time)));
  EXPECT_TRUE(IsSymbolicConstantName(SPELL(sv_sim_time)));

  EXPECT_FALSE(IsFunctionOrTypeName(SPELL(sv_x)));
}

TEST(SvdpiNamingConventions, MacroNamesUseSvUnderscoreUppercase) {
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_MASK(4), 0xFu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFu, 4), 0xFu);
  const unsigned kSignedBitsValue = 0xFu;
  const int kSignedBitsWidth = 4;
  EXPECT_EQ(SV_GET_SIGNED_BITS(kSignedBitsValue, kSignedBitsWidth), 0xFu);

  EXPECT_TRUE(IsMacroName(SPELL(SV_PACKED_DATA_NELEMS)));
  EXPECT_TRUE(IsMacroName(SPELL(SV_MASK)));
  EXPECT_TRUE(IsMacroName(SPELL(SV_GET_UNSIGNED_BITS)));
  EXPECT_TRUE(IsMacroName(SPELL(SV_GET_SIGNED_BITS)));

  EXPECT_FALSE(IsFunctionOrTypeName(SPELL(SV_GET_UNSIGNED_BITS)));
}

#define FUNCTION_NAME(fn) ((void)sizeof(&(fn)), std::string_view(#fn))
#define TYPE_NAME(t) ((void)sizeof(t), std::string_view(#t))
#define CONSTANT_NAME(c) ((void)(c), std::string_view(#c))

std::vector<std::string_view> EveryFunctionName() {
  return {FUNCTION_NAME(svAckDisabledState),
          FUNCTION_NAME(svDimensions),
          FUNCTION_NAME(svDpiVersion),
          FUNCTION_NAME(svGetArrayPtr),
          FUNCTION_NAME(svGetArrElemPtr),
          FUNCTION_NAME(svGetArrElemPtr1),
          FUNCTION_NAME(svGetArrElemPtr2),
          FUNCTION_NAME(svGetArrElemPtr3),
          FUNCTION_NAME(svGetBitArrElem),
          FUNCTION_NAME(svGetBitArrElem1),
          FUNCTION_NAME(svGetBitArrElem1VecVal),
          FUNCTION_NAME(svGetBitArrElem2),
          FUNCTION_NAME(svGetBitArrElem2VecVal),
          FUNCTION_NAME(svGetBitArrElem3),
          FUNCTION_NAME(svGetBitArrElem3VecVal),
          FUNCTION_NAME(svGetBitArrElemVecVal),
          FUNCTION_NAME(svGetBitselBit),
          FUNCTION_NAME(svGetBitselLogic),
          FUNCTION_NAME(svGetCallerInfo),
          FUNCTION_NAME(svGetLogicArrElem),
          FUNCTION_NAME(svGetLogicArrElem1),
          FUNCTION_NAME(svGetLogicArrElem1VecVal),
          FUNCTION_NAME(svGetLogicArrElem2),
          FUNCTION_NAME(svGetLogicArrElem2VecVal),
          FUNCTION_NAME(svGetLogicArrElem3),
          FUNCTION_NAME(svGetLogicArrElem3VecVal),
          FUNCTION_NAME(svGetLogicArrElemVecVal),
          FUNCTION_NAME(svGetNameFromScope),
          FUNCTION_NAME(svGetPartselBit),
          FUNCTION_NAME(svGetPartselLogic),
          FUNCTION_NAME(svGetScope),
          FUNCTION_NAME(svGetScopeFromName),
          FUNCTION_NAME(svGetTime),
          FUNCTION_NAME(svGetTimePrecision),
          FUNCTION_NAME(svGetTimeUnit),
          FUNCTION_NAME(svGetUserData),
          FUNCTION_NAME(svHigh),
          FUNCTION_NAME(svIncrement),
          FUNCTION_NAME(svIsDisabledState),
          FUNCTION_NAME(svLeft),
          FUNCTION_NAME(svLow),
          FUNCTION_NAME(svPutBitArrElem),
          FUNCTION_NAME(svPutBitArrElem1),
          FUNCTION_NAME(svPutBitArrElem1VecVal),
          FUNCTION_NAME(svPutBitArrElem2),
          FUNCTION_NAME(svPutBitArrElem2VecVal),
          FUNCTION_NAME(svPutBitArrElem3),
          FUNCTION_NAME(svPutBitArrElem3VecVal),
          FUNCTION_NAME(svPutBitArrElemVecVal),
          FUNCTION_NAME(svPutBitselBit),
          FUNCTION_NAME(svPutBitselLogic),
          FUNCTION_NAME(svPutLogicArrElem),
          FUNCTION_NAME(svPutLogicArrElem1),
          FUNCTION_NAME(svPutLogicArrElem1VecVal),
          FUNCTION_NAME(svPutLogicArrElem2),
          FUNCTION_NAME(svPutLogicArrElem2VecVal),
          FUNCTION_NAME(svPutLogicArrElem3),
          FUNCTION_NAME(svPutLogicArrElem3VecVal),
          FUNCTION_NAME(svPutLogicArrElemVecVal),
          FUNCTION_NAME(svPutPartselBit),
          FUNCTION_NAME(svPutPartselLogic),
          FUNCTION_NAME(svPutUserData),
          FUNCTION_NAME(svRight),
          FUNCTION_NAME(svSetScope),
          FUNCTION_NAME(svSize),
          FUNCTION_NAME(svSizeOfArray)};
}

std::vector<std::string_view> EveryTypeName() {
  return {TYPE_NAME(svBit),
          TYPE_NAME(svBitVecVal),
          TYPE_NAME(svLogic),
          TYPE_NAME(svLogicVecVal),
          TYPE_NAME(svOpenArrayHandle),
          TYPE_NAME(svScalar),
          TYPE_NAME(svScope),
          TYPE_NAME(svTimeVal)};
}

std::vector<std::string_view> EveryConstantName() {
  return {CONSTANT_NAME(sv_0),
          CONSTANT_NAME(sv_1),
          CONSTANT_NAME(sv_x),
          CONSTANT_NAME(sv_z),
          CONSTANT_NAME(sv_scaled_real_time),
          CONSTANT_NAME(sv_sim_time)};
}

std::vector<std::string_view> EveryMacroName() {
  return {SPELL(SV_PACKED_DATA_NELEMS), SPELL(SV_MASK),
          SPELL(SV_GET_UNSIGNED_BITS), SPELL(SV_GET_SIGNED_BITS)};
}

TEST(SvdpiNamingConventions, EveryNameTheHeaderIntroducesConforms) {
  const std::vector<std::string_view> kFunctions = EveryFunctionName();
  const std::vector<std::string_view> kTypes = EveryTypeName();
  const std::vector<std::string_view> kConstants = EveryConstantName();
  const std::vector<std::string_view> kMacros = EveryMacroName();
  EXPECT_EQ(kFunctions.size(), 66u);
  EXPECT_EQ(kTypes.size(), 8u);
  for (std::string_view n : kFunctions) {
    EXPECT_TRUE(HasInterfacePrefix(n)) << n;
    EXPECT_TRUE(IsFunctionOrTypeName(n)) << n;
    EXPECT_FALSE(IsSymbolicConstantName(n)) << n;
    EXPECT_FALSE(IsMacroName(n)) << n;
  }
  for (std::string_view n : kTypes) {
    EXPECT_TRUE(HasInterfacePrefix(n)) << n;
    EXPECT_TRUE(IsFunctionOrTypeName(n)) << n;
  }
  for (std::string_view n : kConstants) {
    EXPECT_TRUE(HasInterfacePrefix(n)) << n;
    EXPECT_TRUE(IsSymbolicConstantName(n)) << n;
    EXPECT_FALSE(IsFunctionOrTypeName(n)) << n;
    EXPECT_FALSE(IsMacroName(n)) << n;
  }
  for (std::string_view n : kMacros) {
    EXPECT_TRUE(HasInterfacePrefix(n)) << n;
    EXPECT_TRUE(IsMacroName(n)) << n;
    EXPECT_FALSE(IsFunctionOrTypeName(n)) << n;
    EXPECT_FALSE(IsSymbolicConstantName(n)) << n;
  }
}

}  // namespace
}  // namespace delta
