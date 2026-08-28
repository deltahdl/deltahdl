#include <cstdint>
#include <string>

#include "fixture_vcd_dump_from_source.h"
#include "helpers_text_lines.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §21.7.2.1, the prose under Syntax 21-20: "Next, the file contains definitions
// of the scope and type of variables being dumped, followed by the actual value
// changes at each simulation time increment. Only the variables that change
// value during a time increment are listed." The second sentence bounds the
// listing to the variables that changed; the first requires the changes
// themselves to be there. A variable that did change during an increment and is
// listed under no increment satisfies neither, and the dump reads as a waveform
// the object never took.
//
// The cases below all put a dumped variable under an event control, because
// that is what the dumper's change detection shares state with. The detection
// compares a dumped object against Variable::prev_value, and EventAwaiter in
// src/simulator/awaiters.h writes that same field: at awaiters.h:205 when a
// watcher runs, and at awaiters.h:262 when the change it saw was not the edge
// the process asked for. A source whose only process is an initial block with
// delays cannot tell the two apart, so each case here drives one process
// against another.
//
// Each case runs through the production path -- the source's own $dumpfile and
// $dumpvars open the file, register the objects and install the per-timestep
// recording -- because the subject is which records reach the file that a run
// of this source leaves behind. VcdDumpRunTestBase in
// lib/cpp/test_fixtures/fixture_vcd_dump_run.h would install a writer of its
// own before the run, and its kAllVariablesSorted registration would put the
// objects in the file whatever the source asked for; neither is wanted where
// the claim is about the file a design writes for itself.
class VcdChangeDetectionFromSource : public VcdDumpFromSourceTestBase {
 protected:
  // The dump file every source below names. Relative, so it lands in the
  // scratch directory the fixture stands the run in.
  static constexpr const char* kDumpName = "edges.vcd";

  // A module driving `clk` through four edges -- 0 at time 0, then 1, 0, 1, 0
  // at five-time-unit intervals -- from one initial block, with `waiter`
  // spliced in beside it as a second process. Every case that varies only the
  // waiter builds its source here, so the two runs it compares differ in the
  // waiter and in nothing else: the same declarations, the same dump tasks and
  // the same drive.
  //
  // The drive alternates rather than settling, so an edge of each direction
  // falls under a distinct time increment. A clock held at one value after its
  // first edge would be recorded correctly by a dumper that never detects a
  // change after the first and by one that detects every change alike.
  static std::string ClockSource(const std::string& waiter) {
    return std::string(
               "module t;\n"
               "  logic clk;\n"
               "  integer n;\n"
               "  initial begin\n"
               "    clk = 1'b0;\n"
               "    n = 0;\n"
               "    $dumpfile(\"") +
           kDumpName +
           "\");\n"
           "    $dumpvars;\n"
           "    #5 clk = 1'b1;\n"
           "    #5 clk = 1'b0;\n"
           "    #5 clk = 1'b1;\n"
           "    #5 clk = 1'b0;\n"
           "  end\n" +
           waiter + "endmodule\n";
  }

  // Runs `src` and returns the value characters the dump recorded for the
  // object named `name`, in file order. "<not-declared>" says the run declared
  // no such object, which a case reads as its source never having reached the
  // dump tasks at all.
  std::string ValuesRecordedFor(const std::string& src,
                                const std::string& name) {
    RunSource(src);
    const std::string content = DumpFile(kDumpName);
    const std::string code = IdentCodeFor(content, name);
    if (code.empty()) return "<not-declared>";
    return ScalarChanges(content, code);
  }

  // How many times the module's waiter resumed, which every waiter below
  // counts into `n`; a source with no waiter leaves it at the 0 its initial
  // block assigned. A case reads this so that a dump missing nothing cannot be
  // a source whose waiter never armed.
  uint64_t WaiterResumes() {
    Variable* var = f_.ctx.FindVariable("n");
    return var == nullptr ? UINT64_MAX : var->value.ToUint64();
  }

 private:
  // The identifier_code the file's $var declaration gave `name` (Syntax 21-20:
  // $var var_type size identifier_code reference $end), or "" when the file
  // declares no such object. Read off the reference rather than assumed,
  // because the codes are handed out in registration order.
  static std::string IdentCodeFor(const std::string& content,
                                  const std::string& name) {
    for (const auto& line : AllLines(content)) {
      auto toks = Tokens(line);
      if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) {
        return toks[3];
      }
    }
    return std::string();
  }

  // Syntax 21-20: value ::= 0 | 1 | x | X | z | Z.
  static bool IsValueCharacter(char c) {
    return c == '0' || c == '1' || c == 'x' || c == 'X' || c == 'z' || c == 'Z';
  }

  // Every scalar_value_change carrying `code`, reduced to its value character
  // and kept in file order (Syntax 21-20: scalar_value_change ::= value
  // identifier_code, which the writer emits as one line joining the two). The
  // resulting string is the waveform the file claims the object took, the
  // $dumpvars checkpoint's opening record first.
  //
  // The leading character is checked against the value production above so
  // that a simulation_time command sharing the length and the trailing
  // character of a record -- #5 against the identifier code 5 -- is not read
  // as one.
  static std::string ScalarChanges(const std::string& content,
                                   const std::string& code) {
    std::string values;
    for (const auto& line : AllLines(content)) {
      if (line.size() != code.size() + 1) continue;
      if (!IsValueCharacter(line[0])) continue;
      if (line.compare(1, code.size(), code) == 0) values.push_back(line[0]);
    }
    return values;
  }
};

// §21.7.2.1: "Only the variables that change value during a time increment are
// listed" -- so a clock that changes under each of four increments is listed
// under each of them, and the file reads 0 (the $dumpvars checkpoint), then 1,
// 0, 1, 0. The clock is driven from one process and waited on from another,
// which is the arrangement the dumper's change detection shares
// Variable::prev_value with: awaiters.h:205 restores the watcher's own
// baseline into that field and awaiters.h:262 resyncs it whenever the change
// was not a posedge, and either write lands between the assignment and the
// end-of-increment recording pass.
TEST_F(VcdChangeDetectionFromSource, ClockWaitedOnByPosedgeRecordsEveryEdge) {
  const std::string values = ValuesRecordedFor(
      ClockSource("  always @(posedge clk) n = n + 1;\n"), "clk");

  // Two posedges reached the waiter, so the source did arm an edge watcher on
  // the dumped clock rather than merely declaring one.
  EXPECT_EQ(WaiterResumes(), 2U);
  EXPECT_EQ(values, "01010");
}

// §21.7.2.1: the same four increments and the same four changes, with the
// waiter gone. The value characters are the same string, so the case above is
// making a claim about the waiter rather than about the number four: a dump of
// this design records every edge, and adding a process that waits on the clock
// is not one of the things §21.7.2.1 lets change what is listed.
TEST_F(VcdChangeDetectionFromSource, ClockWithNoWaiterRecordsEveryEdge) {
  const std::string values = ValuesRecordedFor(ClockSource(""), "clk");

  EXPECT_EQ(WaiterResumes(), 0U);
  EXPECT_EQ(values, "01010");
}

// §21.7.2.1: a variable that changes during a time increment is listed under
// it, and the standard conditions that on the change alone -- not on any
// process having been resumed by it. `v` starts at 1, takes the negedge its
// watcher asked for at #5, and then takes a posedge at #10 that the watcher has
// no use for. That second change is the arm this case is about:
// EventAwaiter::EdgeGatePasses (src/simulator/awaiters.h:262) resyncs
// Variable::prev_value to the new value and returns without resuming anybody,
// so nothing but the dump is left to notice the change. All three increments
// are owed their record, and the file reads 1 for the $dumpvars checkpoint,
// then 0 and 1.
TEST_F(VcdChangeDetectionFromSource, PosedgeUnderANegedgeWaitIsStillRecorded) {
  const std::string values =
      ValuesRecordedFor(std::string("module t;\n"
                                    "  logic v;\n"
                                    "  integer n;\n"
                                    "  initial begin\n"
                                    "    v = 1'b1;\n"
                                    "    n = 0;\n"
                                    "    $dumpfile(\"") +
                            kDumpName +
                            "\");\n"
                            "    $dumpvars;\n"
                            "    #5 v = 1'b0;\n"
                            "    #5 v = 1'b1;\n"
                            "  end\n"
                            "  always @(negedge v) n = n + 1;\n"
                            "endmodule\n",
                        "v");

  // The negedge at #5 resumed the waiter and the posedge at #10 did not, so
  // the watcher was armed over the change this case is about and still passed
  // it over -- which is what separates this arm from the posedge case above.
  EXPECT_EQ(WaiterResumes(), 1U);
  EXPECT_EQ(values, "101");
}

}  // namespace
