#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
// §6.22.6 only defines the matching relation, listing a) "A nettype matches
// itself and the nettype of nets declared using that nettype within the scope
// of the nettype type identifier" and b) the renaming case; the "shall" the
// report enforces is §28.8's "A bidirectional switch shall not connect nets of
// two different user-defined net types or a user-defined net type and a
// built-in net type", so the report names §28.8.
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
  // The two nettype names are in the substring because
  // CheckBidirNettypeCompatibility in src/elaborator/elaborator_gates.cpp has a
  // sibling report under the same subclause, for a user-defined nettype tied to
  // a built-in net, and both begin "bidirectional pass switch cannot connect".
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot connect different user-defined nettypes "
                            "('foo_t' and 'bar_t')",
                            6, "28.8"));
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
