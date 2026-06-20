#include <gtest/gtest.h>

#include <cctype>
#include <string_view>

// Annex H.3 governs the names introduced by the DPI C layer. That layer is
// carried by svdpi.h, so this test includes it directly and observes the
// spelling of the identifiers it actually defines. svdpi.h is included alone
// here: it intentionally redefines a few VPI names, so it must not share a
// translation unit with vpi.h.
#include "simulator/svdpi.h"

namespace delta {
namespace {

// Capture the source spelling of an identifier token. The single-level form is
// deliberate: the # operator stringifies its argument without macro-expanding
// it, so SPELL(sv_x) yields "sv_x" rather than the value sv_x expands to. This
// is what lets the convention checks below inspect the name svdpi.h declares
// rather than whatever it stands for.
#define SPELL(name) #name

// §H.3 bullet 1: every interface name carries the sv or SV_ prefix.
bool HasInterfacePrefix(std::string_view n) {
  return n.starts_with("sv") || n.starts_with("SV_");
}

// §H.3 bullet 2: function and type names begin with sv and continue in
// initially-capitalized words with no separators, e.g., svLogicVecVal. The
// checkable lexical signature is: sv, an uppercase letter starting the first
// word, and no underscore anywhere.
bool IsFunctionOrTypeName(std::string_view n) {
  return n.size() > 2 && n[0] == 's' && n[1] == 'v' &&
         std::isupper(static_cast<unsigned char>(n[2])) &&
         n.find('_') == std::string_view::npos;
}

// §H.3 bullet 3: symbolic-constant names start with the lowercase sv_ prefix.
bool IsSymbolicConstantName(std::string_view n) { return n.starts_with("sv_"); }

// §H.3 bullet 4: macro-definition names start with SV_ and are spelled in
// all-uppercase words separated by underscores, e.g., SV_GET_UNSIGNED_BITS.
// "All uppercase words" is checked by the absence of any lowercase letter.
bool IsMacroName(std::string_view n) {
  if (!n.starts_with("SV_")) return false;
  for (char c : n) {
    if (std::islower(static_cast<unsigned char>(c))) return false;
  }
  return true;
}

// §H.3 bullet 1: a representative name from each of the four categories defined
// by svdpi.h carries the sv/SV_ prefix. Each name is also used (as a value,
// type, function, or macro) so the test only compiles if svdpi.h truly
// introduces it under that spelling.
TEST(SvdpiNamingConventions, EveryInterfaceNameHasSvPrefix) {
  EXPECT_EQ(sv_x, 3);         // symbolic constant
  svLogicVecVal vec_value{};  // type
  (void)vec_value;
  EXPECT_GT(sizeof(&svGetScope), 0u);  // function (declaration referenced)
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFFFFFFFu, 4), 0xFu);  // macro

  EXPECT_TRUE(HasInterfacePrefix(SPELL(sv_x)));
  EXPECT_TRUE(HasInterfacePrefix(SPELL(svLogicVecVal)));
  EXPECT_TRUE(HasInterfacePrefix(SPELL(svGetScope)));
  EXPECT_TRUE(HasInterfacePrefix(SPELL(SV_GET_UNSIGNED_BITS)));
}

// §H.3 bullet 2: the function and type names svdpi.h declares are sv-prefixed
// camel case with no separators. The entities are referenced so their
// declarations in svdpi.h back the spellings under test.
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

  // A camel-case name carries no underscore, distinguishing it from the
  // constant and macro categories.
  EXPECT_FALSE(IsSymbolicConstantName(SPELL(svLogicVecVal)));
  EXPECT_FALSE(IsMacroName(SPELL(svLogicVecVal)));
}

// §H.3 bullet 3: the symbolic constants svdpi.h defines (the 4-state scalar
// codes and the time-form selectors) start with sv_. Their values are exercised
// so the named constants must be present for the test to compile.
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

  // The sv_ prefix sets these apart from camel-case function/type names.
  EXPECT_FALSE(IsFunctionOrTypeName(SPELL(sv_x)));
}

// §H.3 bullet 4: macro definitions are spelled SV_ followed by uppercase words
// separated by underscores. Each macro is invoked so svdpi.h must define it,
// and the spelling is then checked against the convention.
TEST(SvdpiNamingConventions, MacroNamesUseSvUnderscoreUppercase) {
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_MASK(4), 0xFu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFu, 4), 0xFu);
  EXPECT_EQ(SV_GET_SIGNED_BITS(0xFu, 4), 0xFu);

  EXPECT_TRUE(IsMacroName(SPELL(SV_PACKED_DATA_NELEMS)));
  EXPECT_TRUE(IsMacroName(SPELL(SV_MASK)));
  EXPECT_TRUE(IsMacroName(SPELL(SV_GET_UNSIGNED_BITS)));
  EXPECT_TRUE(IsMacroName(SPELL(SV_GET_SIGNED_BITS)));

  // The all-uppercase macro spelling is distinct from a camel-case name.
  EXPECT_FALSE(IsFunctionOrTypeName(SPELL(SV_GET_UNSIGNED_BITS)));
}

}  // namespace
}  // namespace delta
