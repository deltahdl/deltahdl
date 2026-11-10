#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

TEST(Elaboration, EventVarIsEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "ev") {
      found = true;
      EXPECT_TRUE(v.is_event);
    }
  }
  EXPECT_TRUE(found) << "event variable 'ev' not found";
}

TEST(Elaboration, EventVarWidthZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "ev") {
      EXPECT_EQ(v.width, 0u);
    }
  }
}

TEST(Elaboration, EventAssignNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev = null;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EventAliasInitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  const RtlirVariable* done_too = nullptr;
  for (const auto& v : mod->variables) {
    if (v.name == "done_too") done_too = &v;
  }
  ASSERT_NE(done_too, nullptr);
  EXPECT_TRUE(done_too->is_event);
  ASSERT_NE(done_too->init_expr, nullptr);
  EXPECT_EQ(done_too->init_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(done_too->init_expr->text, "done");
}

constexpr std::string_view kFromOther =
    "event can only be assigned from another event or null";
constexpr std::string_view kToOther =
    "event cannot be assigned to a non-event variable";
constexpr std::string_view kCompared =
    "event can only be compared with another event or null";

std::string InEveryPlace(std::string_view body) {
  std::string decls = "event e, f;\n  int i;\n  string s;\n";
  return std::string("package k;\n  ")
      .append(decls)
      .append("  function void p();\n    ")
      .append(body)
      .append("\n  endfunction\nendpackage\nclass C;\n  ")
      .append(decls)
      .append("  function void m();\n    ")
      .append(body)
      .append("\n  endfunction\nendclass\n")
      .append(decls)
      .append("function void u();\n  ")
      .append(body)
      .append("\nendfunction\ninterface ifc;\n  ")
      .append(decls)
      .append("  initial begin\n    ")
      .append(body)
      .append("\n  end\nendinterface\nprogram pg;\n  ")
      .append(decls)
      .append("  initial begin\n    ")
      .append(body)
      .append("\n  end\nendprogram\nmodule t;\n  ifc ii();\n  pg pp();\n  ")
      .append(decls)
      .append("  if (1) begin : g\n    ")
      .append(decls)
      .append("    initial begin\n      ")
      .append(body)
      .append("\n    end\n  end\n  initial begin\n    ")
      .append(body)
      .append("\n  end\nendmodule\n");
}

TEST(Elaboration,
     DISABLED_AnEventAssignedOrComparedWithAnotherTypeIsReportedEverywhere) {
  const struct {
    const char* body;
    std::string_view message;
  } kForms[] = {
      {"e = 5;", kFromOther},
      {"e = s;", kFromOther},
      {"i = e;", kToOther},
      {"i = e == 1;", kCompared},
  };
  for (const auto& form : kForms) {
    SCOPED_TRACE(form.body);
    std::string src = InEveryPlace(form.body);
    ElabFixture f;
    ElaborateSrc(src, f);
    int reported = 0;
    for (std::string::size_type at = src.find(form.body);
         at != std::string::npos; at = src.find(form.body, at + 1)) {
      auto line = static_cast<uint32_t>(
          1 + std::count(src.begin(),
                         src.begin() + static_cast<std::ptrdiff_t>(at), '\n'));
      if (ReportedError(f.diag.Diagnostics(), form.message, line, "6.17")) {
        ++reported;
      }
    }
    EXPECT_EQ(reported, 7);
  }
}

TEST(Elaboration,
     AnEventAssignedAnEventOrNullAndComparedWithThemIsAcceptedEverywhere) {
  EXPECT_TRUE(ElabOk(InEveryPlace(
      "e = f;\n    f = null;\n    i = e == f;\n    i = e != null;\n"
      "    i = null === e;")));
}

}  // namespace
