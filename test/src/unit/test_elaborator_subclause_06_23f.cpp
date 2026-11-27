#include <gtest/gtest.h>

#include <array>
#include <format>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_declaration_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kParams =
    "  int nq [$];\n"
    "  int na [3];\n"
    "  localparam type(nq) PTQ = '{1, 2};\n"
    "  localparam type(na) PTA = '{1, 2, 3};\n"
    "  localparam int SQ [$] = '{1, 2};\n"
    "  localparam int SA [3] = '{1, 2, 3};\n"
    "  int x;\n";

constexpr std::string_view kReport =
    "'$' may stand only in a queue's dimension or select";

TEST(ParameterOfTypeReferenceElaborator, FixedSizeArrayRefusesDollarSelect) {
  for (std::string_view select : {"PTA[$]", "SA[$]"}) {
    const std::string kBody =
        std::format("{}  initial x = {};\n", kParams, select);
    ExpectReportedIn({"module", "interface", "program"}, kBody, kReport, select,
                     "6.20.7");
  }
}

TEST(ParameterOfTypeReferenceElaborator, QueueTakesDollarSelect) {
  const std::string kBody =
      std::format("{}{}", kParams,
                  "  initial x = PTQ[$] + PTQ.size() + PTA[2] + $size(PTA);\n"
                  "  initial x = SQ[$] + SQ.size() + SA[2] + $size(SA);\n");
  ExpectCleanIn({"module", "interface", "program", "generate block"}, kBody);
}

struct GenerateForm {
  const char* name;
  const char* text;
};

constexpr std::array kGenerateForms = {
    GenerateForm{"conditional generate block",
                 "module m;\n  if (1) begin : g\n{}  end\nendmodule\n"},
    GenerateForm{"loop generate block",
                 "module m;\n  for (genvar i = 0; i < 1; i++) begin : l\n{}"
                 "  end\nendmodule\n"},
    GenerateForm{"case generate block",
                 "module m;\n  case (1)\n    1: begin : c\n{}    end\n"
                 "  endcase\nendmodule\n"},
};

std::string InGenerate(const GenerateForm& form, std::string_view body) {
  return std::vformat(form.text, std::make_format_args(body));
}

TEST(ParameterOfTypeReferenceElaborator,
     FixedSizeArrayRefusesDollarSelectInAGenerateBlock) {
  for (std::string_view select : {"PTA[$]", "SA[$]"}) {
    const std::string kBody =
        std::format("{}  initial x = {};\n", kParams, select);
    for (const GenerateForm& form : kGenerateForms) {
      const std::string kSrc = InGenerate(form, kBody);
      SCOPED_TRACE(kSrc);
      ElabFixture f;
      ElaborateSrc(kSrc, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport,
                                LineHolding(kSrc, select), "6.20.7"));
    }
  }
}

TEST(ParameterOfTypeReferenceElaborator,
     QueueTakesDollarSelectInAGenerateBlock) {
  const std::string kBody =
      std::format("{}{}", kParams,
                  "  initial x = PTQ[$] + PTQ.size() + PTA[2] + $size(PTA);\n"
                  "  initial x = SQ[$] + SQ.size() + SA[2] + $size(SA);\n");
  for (const GenerateForm& form : kGenerateForms) {
    const std::string kSrc = InGenerate(form, kBody);
    SCOPED_TRACE(kSrc);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_FALSE(f.has_errors);
  }
}

}  // namespace
