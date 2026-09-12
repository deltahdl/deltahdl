// Annex C.2.8: operator overloading.
//
// IEEE 1800-2017 deprecated the operator overloading construct of IEEE
// 1800-2012 §11.11, whose overload_declaration was written `bind
// overload_operator function data_type function_identifier (
// overload_proto_formals ) ;`, and neither the subclause nor its syntax appears
// in this version of the standard, where `bind` opens §23.11's bind directive
// alone. A `bind` followed by an operator is the removed construct and nothing
// else, so the parser reports it as removed under C.2.8 at the operator, reads
// on to the ';' that ended the declaration, and records no bind directive for
// it; a bind directive with a target is what §23.11 keeps.

#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The 2012 form with a binary operator, written in a module body.
TEST(OperatorOverloadingDeprecated, BindOfBinaryOperatorIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  bind + function int add(int a, int b);\n"
      "  int x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "operator overloading has been removed", 2,
                            "C.2.8"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->bind_directives.empty());
  // The declaration was read to its ';', so the item behind it is the
  // module's.
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl));
}

// The same form at compilation-unit scope, with the assignment operator, which
// the 2012 list ended on; nothing is recorded among the unit's bind directives.
TEST(OperatorOverloadingDeprecated, BindOfAssignmentOperatorAtUnitScope) {
  auto r = Parse(
      "bind = function int conv(real r);\n"
      "module m; endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "operator overloading has been removed", 1,
                            "C.2.8"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->bind_directives.empty());
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

// Every operator the 2012 overload_operator listed is the removed construct.
TEST(OperatorOverloadingDeprecated, EveryOverloadableOperatorIsRejected) {
  const char* const kOperators[] = {"+",  "++", "-", "--", "*", "**", "/", "%",
                                    "==", "!=", "<", "<=", ">", ">=", "="};
  for (const char* op : kOperators) {
    auto r = Parse(std::string("module m;\n  bind ") + op +
                   " function int f(int a);\nendmodule\n");
    EXPECT_TRUE(ReportedError(r.diags, "operator overloading has been removed",
                              2, "C.2.8"))
        << op;
  }
}

// §23.11's bind directive, whose target is an identifier, is the form that
// stays.
TEST(OperatorOverloadingDeprecated, BindDirectiveStillParses) {
  auto r = Parse(
      "module target; endmodule\n"
      "module binder; endmodule\n"
      "module m;\n"
      "  bind target binder b1();\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[2]->bind_directives.size(), 1u);
}

}  // namespace
