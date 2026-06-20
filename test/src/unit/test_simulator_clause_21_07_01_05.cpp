#include "builders_systask.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Drives the $dumplimit system task end to end so that the size-limiting
// semantics of §21.7.1.5 are observed as the production task path applies them.
class DumplimitSysTask : public VcdTestBase {};

// The filesize argument bounds the dump file in bytes: once the VCD file grows
// past the limit the dumper stops and a comment marking the limit is inserted,
// while earlier value changes written below the limit are retained.
TEST_F(DumplimitSysTask, LimitReachedStopsDumpAndInsertsComment) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    f.ctx.SetVcdWriter(&vcd);
    // Set a modest byte budget through the production $dumplimit task path; the
    // header fits, but repeated value changes will eventually overrun it.
    EvalExpr(MkSysCall(f.arena, "$dumplimit", {MkInt(f.arena, 200)}), f.ctx,
             f.arena);
    data->prev_value = MakeLogic4VecVal(f.arena, 8, 0x00);
    for (uint64_t t = 1; t <= 40; ++t) {
      data->value = MakeLogic4VecVal(f.arena, 8, t & 0xFF);
      vcd.WriteTimestamp(t * 10);
      vcd.DumpChangedValues(0);
      data->prev_value = data->value;
    }
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("#10\n"), std::string::npos);  // early dump retained
  EXPECT_NE(content.find("$comment"),
            std::string::npos);                          // limit comment added
  EXPECT_EQ(content.find("#400\n"), std::string::npos);  // late dumps stopped
}

// Only one limit comment is written: once the threshold is crossed every later
// dump attempt is dropped by the latch rather than re-emitting the marker.
TEST_F(DumplimitSysTask, LimitCommentInsertedOnlyOnce) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumplimit", {MkInt(f.arena, 200)}), f.ctx,
             f.arena);
    data->prev_value = MakeLogic4VecVal(f.arena, 8, 0x00);
    // Keep dumping well past the limit so many post-limit attempts occur.
    for (uint64_t t = 1; t <= 40; ++t) {
      data->value = MakeLogic4VecVal(f.arena, 8, t & 0xFF);
      vcd.WriteTimestamp(t * 10);
      vcd.DumpChangedValues(0);
      data->prev_value = data->value;
    }
  }
  auto content = ReadVcd();
  size_t count = 0;
  for (size_t p = content.find("Dump limit of"); p != std::string::npos;
       p = content.find("Dump limit of", p + 1)) {
    ++count;
  }
  EXPECT_EQ(count,
            1u);  // marker emitted exactly once despite repeated attempts
}

// When the file stays below the configured limit the dumper behaves as if no
// limit were set: every value change is written and no limit comment appears.
TEST_F(DumplimitSysTask, DumpingContinuesWhenBelowLimit) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0x00);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("data", 8, data);  // ident '!'
    vcd.EndDefinitions();
    f.ctx.SetVcdWriter(&vcd);
    EvalExpr(MkSysCall(f.arena, "$dumplimit", {MkInt(f.arena, 1000000)}), f.ctx,
             f.arena);
    data->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
    data->prev_value = MakeLogic4VecVal(f.arena, 8, 0x00);
    vcd.WriteTimestamp(100);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // no limit comment
  EXPECT_NE(content.find("#100\n"), std::string::npos);    // dumping continued
  EXPECT_NE(content.find("b11111111 !"), std::string::npos);  // change written
}

}  // namespace
}  // namespace delta
