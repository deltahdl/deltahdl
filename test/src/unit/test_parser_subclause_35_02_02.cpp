#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string ImportTaking(const std::string& formal) {
  return "module m;\n  import \"DPI-C\" function void f(" + formal +
         ");\nendmodule\n";
}

struct ForeignFormal {
  const char* formal;
  const char* message;
};

constexpr ForeignFormal kForeignFormals[] = {
    {"int* p", "expected ')', got '*'"},
    {"char c", "expected ')', got identifier"},
    {"unsigned int u", "expected ')', got 'int'"}};

TEST(DpiForeignTypeSyntax, AForeignTypeWrittenAsAnImportFormalIsReported) {
  for (const auto& foreign : kForeignFormals) {
    auto r = Parse(ImportTaking(foreign.formal));
    EXPECT_TRUE(ReportedError(r.diags, foreign.message, 2, "13.3"))
        << foreign.formal;
  }
}

TEST(DpiForeignTypeSyntax, TheSystemVerilogTypesNearestThemAreAccepted) {
  for (const char* formal : {"chandle p", "byte c", "int unsigned u"}) {
    auto r = Parse(ImportTaking(formal));
    EXPECT_FALSE(r.has_errors) << formal;
  }
}

TEST(DpiForeignTypeSyntax, AForeignPointerResultIsReported) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function char* g();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got '*'", 2, "35.5.4"));
}

TEST(DpiForeignTypeSyntax, AStringResultInItsPlaceIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function string g();\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(DpiForeignTypeSyntax, ATypeNamedCharInScopeIsASystemVerilogType) {
  auto r = Parse(
      "module m;\n"
      "  typedef byte char;\n"
      "  import \"DPI-C\" function char g(input char c);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
