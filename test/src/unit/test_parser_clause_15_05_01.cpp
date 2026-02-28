// §15.5.1: Triggering an event

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// event_trigger ::=
//   -> hierarchical_event_identifier nonrange_select ;
//   | ->> [ delay_or_event_control ] hierarchical_event_identifier
//     nonrange_select ;
// ---------------------------------------------------------------------------
// §15.5.1: blocking event trigger
TEST(ParserA605, EventTriggerBlocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> ev;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

}  // namespace
