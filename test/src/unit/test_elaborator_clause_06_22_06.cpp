#include <string_view>
#include <unordered_map>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.22.6 Matching nettypes, exercised directly through the production matching
// predicate. `nettype_canonical` maps each nettype name to the canonical
// (source) nettype it resolves to, which is how an alias is tied to the nettype
// it renames.
std::unordered_map<std::string_view, std::string_view> SampleNettypeCanonical() {
  std::unordered_map<std::string_view, std::string_view> canon;
  canon["base_t"] = "base_t";    // a user-defined nettype is its own canonical
  canon["alias_t"] = "base_t";   // alias of base_t resolves to base_t
  canon["other_t"] = "other_t";  // an unrelated nettype
  return canon;
}

// §6.22.6(a): a nettype matches itself.
TEST(MatchingNettypes, NettypeMatchesItself) {
  auto canon = SampleNettypeCanonical();
  EXPECT_TRUE(NettypesMatch("base_t", "base_t", canon));
}

// §6.22.6(b): a simple nettype that renames a user-defined nettype matches that
// user-defined nettype.
TEST(MatchingNettypes, AliasMatchesRenamedNettype) {
  auto canon = SampleNettypeCanonical();
  EXPECT_TRUE(NettypesMatch("base_t", "alias_t", canon));
  EXPECT_TRUE(NettypesMatch("alias_t", "base_t", canon));
}

// §6.22.6: distinct user-defined nettypes do not match, even when they share an
// underlying data type -- matching is by nettype identity, not data type.
TEST(MatchingNettypes, DistinctNettypesDoNotMatch) {
  auto canon = SampleNettypeCanonical();
  EXPECT_FALSE(NettypesMatch("base_t", "other_t", canon));
  EXPECT_FALSE(NettypesMatch("alias_t", "other_t", canon));
}

// §6.22.6(a) end to end: two nets declared with the same nettype carry matching
// nettypes, so connecting them to the two bidirectional terminals of a pass
// switch raises no different-nettype diagnostic.
TEST(MatchingNettypes, SameNettypeTerminalsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic nt;\n"
      "  nt a;\n"
      "  nt b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §6.22.6(b) end to end: a net of an aliasing nettype matches a net of the
// nettype it renames, so the production validator that compares the two pass
// switch terminals does not flag them as different nettypes.
TEST(MatchingNettypes, AliasAndRenamedNettypeTerminalsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic base_t;\n"
      "  nettype base_t alias_t;\n"
      "  base_t a;\n"
      "  alias_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §6.22.6 end to end: two unrelated user-defined nettypes do not match, so the
// production validator rejects connecting their nets across a pass switch.
TEST(MatchingNettypes, DistinctNettypeTerminalsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic foo_t;\n"
      "  nettype logic bar_t;\n"
      "  foo_t a;\n"
      "  bar_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.22.6(b) edge case: renaming is transitive. An alias of an alias still
// renames the original user-defined nettype, so a net of the chained alias
// matches a net of the base nettype and the production validator accepts them.
TEST(MatchingNettypes, AliasOfAliasMatchesBaseNettype) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic base_t;\n"
      "  nettype base_t mid_t;\n"
      "  nettype mid_t leaf_t;\n"
      "  base_t a;\n"
      "  leaf_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §6.22.6(b) edge case: two simple nettypes that each rename the same
// user-defined nettype match each other, since both resolve to that nettype.
TEST(MatchingNettypes, SiblingAliasesOfSameNettypeMatch) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  nettype logic base_t;\n"
      "  nettype base_t left_t;\n"
      "  nettype base_t right_t;\n"
      "  left_t a;\n"
      "  right_t b;\n"
      "  tran sw(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
