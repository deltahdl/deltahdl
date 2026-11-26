#include <gtest/gtest.h>

#include <format>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kReport =
    "argument to mailbox method 'put' is not type-equivalent";

constexpr std::string_view kPackage =
    "package pk;\n"
    "  typedef logic [11:0] t;\n"
    "  logic [8:0] w9;\n"
    "  class K; int m = 5; endclass\n"
    "endpackage\n";

constexpr std::string_view kScopes[][2] = {
    {"module top;\n", "endmodule\n"},
    {"interface itf;\n", "endinterface\nmodule top; itf i(); endmodule\n"},
    {"program p;\n", "endprogram\nmodule top; p i(); endmodule\n"},
};

constexpr std::string_view kNames =
    "  logic [6:0] n;\n"
    "  string s;\n"
    "  localparam logic [2:0] L = 1;\n"
    "  pk::K k;\n"
    "  genvar g;\n";

constexpr int kPutLine = 13;

std::string InEachScope(std::string_view open, std::string_view close,
                        std::string_view body) {
  std::string text(kPackage);
  text.append(open).append(kNames).append(body).append(close);
  return text;
}

void ExpectPutReportedInEachScope(std::string_view mailbox,
                                  std::string_view message) {
  for (const auto& [open, close] : kScopes) {
    const std::string kText = InEachScope(
        open, close,
        std::format("  {} m = new;\n  initial m.put({});\n", mailbox, message));
    SCOPED_TRACE(kText);
    ElabFixture f;
    ElaborateSrc(kText, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kReport, kPutLine, "15.4.9"));
  }
}

void ExpectAcceptedInEachScope(std::string_view body) {
  for (const auto& [open, close] : kScopes) {
    const std::string kText = InEachScope(open, close, body);
    SCOPED_TRACE(kText);
    ElabFixture f;
    ElaborateSrc(kText, f);
    EXPECT_FALSE(f.has_errors);
  }
}

constexpr std::string_view kIntegralOperands[] = {
    "type(n)",      "type(n + 10'd0)",   "type(L)",
    "type(pk::w9)", "type(logic [5:0])",
};

TEST(MailboxOfTypeReferenceElaborator, IntegralOperandRefusesAString) {
  for (std::string_view operand : kIntegralOperands) {
    ExpectPutReportedInEachScope(std::format("mailbox #({})", operand),
                                 "\"ab\"");
  }
}

TEST(MailboxOfTypeReferenceElaborator, IntegralOperandTakesItsOwnType) {
  for (std::string_view operand :
       {"type(n)", "type(n + 10'd0)", "type(L)", "type(pk::w9)", "type(pk::t)",
        "type(logic [5:0])"}) {
    ExpectAcceptedInEachScope(
        std::format("  mailbox #({0}) m = new;\n"
                    "  var {0} v;\n"
                    "  initial begin m.put(v); m.get(v); end\n",
                    operand));
  }
}

TEST(MailboxOfTypeReferenceElaborator, StringOperandRefusesAnInteger) {
  ExpectPutReportedInEachScope("mailbox #(type(s))", "5");
  ExpectPutReportedInEachScope("std::mailbox #(type(s))", "5");
  ExpectPutReportedInEachScope("mailbox #(string)", "5");
  ExpectPutReportedInEachScope("std::mailbox #(string)", "5");
}

TEST(MailboxOfTypeReferenceElaborator, StringOperandTakesAString) {
  ExpectAcceptedInEachScope(
      "  mailbox #(type(s)) m = new;\n"
      "  std::mailbox #(type(s)) d = new;\n"
      "  initial begin m.put(\"ab\"); m.get(s); d.put(s); end\n");
}

TEST(MailboxOfTypeReferenceElaborator, ClassHandleOperandTakesTheHandle) {
  ExpectAcceptedInEachScope(
      "  mailbox #(type(k)) m = new;\n"
      "  initial begin m.put(k); m.get(k); end\n");
}

TEST(MailboxOfTypeReferenceElaborator, TypedefRefusesAnInteger) {
  ElabFixture f;
  ElaborateSrc(InEachScope("module top;\n", "endmodule\n",
                           "  typedef mailbox #(type(s)) mt;\n"
                           "  mt m = new;\n"
                           "  initial m.put(5);\n"),
               f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kReport, kPutLine + 1, "15.4.9"));
}

}  // namespace
