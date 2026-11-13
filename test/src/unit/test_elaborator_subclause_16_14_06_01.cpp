#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kSavedWriteReport =
    "an action block of a procedural concurrent assertion may not modify an "
    "automatic value";

constexpr const char* kWriteDeclarations =
    "  logic clk;\n"
    "  logic [3:0] v;\n"
    "  int s, z;\n"
    "  task automatic t_in(input int x); endtask\n"
    "  task automatic t_out(output int x); x = 0; endtask\n"
    "  task automatic t_inout(inout int x); endtask\n"
    "  task automatic t_ref(ref int x); endtask\n";

constexpr const char* kWritePlaces[] = {"module", "generate", "interface",
                                        "program"};

std::string WriteSource(const std::string& place, const std::string& stmt) {
  std::string procedure = place == "program"
                              ? "  initial begin @(posedge clk);\n"
                              : "  always @(posedge clk) begin\n";
  std::string items =
      kWriteDeclarations + procedure + "    " + stmt + "\n  end\n";
  if (place == "module") return "module t;\n" + items + "endmodule\n";
  if (place == "generate") {
    return "module t;\n  if (1) begin : g\n" + items + "  end\nendmodule\n";
  }
  return place + " w;\n" + items + "end" + place +
         "\nmodule t;\n  w u();\nendmodule\n";
}

struct WriteShape {
  const char* lead;
  const char* expr;
  const char* tail;
};

constexpr WriteShape kLoopVariable = {
    "for (int j = 0; j < 4; j++) x1: ", "v[j]", ""};
constexpr WriteShape kBlockVariable = {
    "begin automatic int k = 1; x1: ", "v[k]", " end"};
constexpr WriteShape kActionOnlyVariable = {
    "begin automatic int m = 1; x1: ", "v[0]", " end"};
constexpr WriteShape kStaticSaved = {"x1: ", "v[const'(s)]", ""};
constexpr WriteShape kStaticUnmentioned = {"x1: ", "v[0]", ""};

std::string ActionForm(const WriteShape& shape, const char* directive,
                       const char* position, const std::string& action) {
  std::string form = shape.lead;
  form.append(directive).append(" (").append(shape.expr).append(") ");
  form.append(position).append(action).append(";").append(shape.tail);
  return form;
}

std::vector<std::string> ActionForms(const WriteShape& shape,
                                     const std::string& action) {
  std::vector<std::string> forms;
  for (const char* directive : {"assert property", "assume property"}) {
    forms.push_back(ActionForm(shape, directive, "", action));
    forms.push_back(ActionForm(shape, directive, "else ", action));
  }
  for (const char* directive : {"cover property", "cover sequence"}) {
    forms.push_back(ActionForm(shape, directive, "", action));
  }
  return forms;
}

void ExpectWriteReported(const WriteShape& shape, const char* action) {
  for (const char* place : kWritePlaces) {
    for (const std::string& form : ActionForms(shape, action)) {
      std::string src = WriteSource(place, form);
      SCOPED_TRACE(src);
      ElabFixture f;
      ElaborateSrc(src, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kSavedWriteReport,
                                LineHolding(src, "x1:"), "16.14.6.1"));
    }
  }
}

void ExpectWriteAccepted(const WriteShape& shape, const char* action) {
  for (const char* place : kWritePlaces) {
    for (const std::string& form : ActionForms(shape, action)) {
      std::string src = WriteSource(place, form);
      SCOPED_TRACE(src);
      ElabFixture f;
      ElaborateSrc(src, f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

constexpr const char* kLoopVariableWrites[] = {
    "j = 7",    "j++",        "--j",      "j += 3",
    "t_out(j)", "t_inout(j)", "t_ref(j)", "begin $display(j); j = 7; end"};

TEST(ProceduralAssertionActionWrite,
     DISABLED_EachWriteOfALoopVariableIsReportedInEachActionOfEachKind) {
  for (const char* action : kLoopVariableWrites) {
    ExpectWriteReported(kLoopVariable, action);
  }
}

TEST(ProceduralAssertionActionWrite,
     DISABLED_AWriteOfAnAutomaticBlockVariableIsReportedInEachPlace) {
  ExpectWriteReported(kBlockVariable, "k = 7");
  ExpectWriteReported(kBlockVariable, "k++");
  ExpectWriteReported(kBlockVariable, "t_out(k)");
}

TEST(ProceduralAssertionActionWrite,
     DISABLED_AWriteOfAnAutomaticOnlyTheActionBlockMentionsIsReported) {
  ExpectWriteReported(kActionOnlyVariable, "m = 7");
  ExpectWriteReported(kActionOnlyVariable, "begin $display(m); m -= 1; end");
}

constexpr const char* kLoopVariableReads[] = {
    "$display(j)", "t_in(j)", "z = j + 1",
    "begin automatic int y; y = j; $display(y); end"};

TEST(ProceduralAssertionActionWrite,
     EachReadOfAnAutomaticIsAcceptedInEachActionOfEachKind) {
  for (const char* action : kLoopVariableReads) {
    ExpectWriteAccepted(kLoopVariable, action);
  }
  ExpectWriteAccepted(kBlockVariable, "$display(k)");
  ExpectWriteAccepted(kActionOnlyVariable, "$display(m)");
}

TEST(ProceduralAssertionActionWrite,
     AWriteOfAStaticVariableIsAcceptedInEachActionOfEachKind) {
  ExpectWriteAccepted(kStaticSaved, "s = 7");
  ExpectWriteAccepted(kStaticSaved, "s++");
  ExpectWriteAccepted(kStaticSaved, "t_out(s)");
  ExpectWriteAccepted(kStaticUnmentioned, "z = 7");
  ExpectWriteAccepted(kStaticUnmentioned, "t_ref(z)");
}

}  // namespace
