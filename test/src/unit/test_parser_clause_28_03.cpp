#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "model_gate_logic.h"

using namespace delta;

namespace {

TEST(PrimitiveGateTypeParsing, AllGateAndSwitchTypes) {
  auto r = Parse(
      "module m;\n"
      "  // cmos_switchtype\n"
      "  cmos (o1, i1, nc1, pc1);\n"
      "  rcmos (o2, i2, nc2, pc2);\n"
      "  // enable_gatetype\n"
      "  bufif0 (o3, i3, e3);\n"
      "  bufif1 (o4, i4, e4);\n"
      "  notif0 (o5, i5, e5);\n"
      "  notif1 (o6, i6, e6);\n"
      "  // mos_switchtype\n"
      "  nmos (o7, i7, c7);\n"
      "  pmos (o8, i8, c8);\n"
      "  rnmos (o9, i9, c9);\n"
      "  rpmos (o10, i10, c10);\n"
      "  // n_input_gatetype\n"
      "  and (o11, a11, b11);\n"
      "  nand (o12, a12, b12);\n"
      "  or (o13, a13, b13);\n"
      "  nor (o14, a14, b14);\n"
      "  xor (o15, a15, b15);\n"
      "  xnor (o16, a16, b16);\n"
      "  // n_output_gatetype\n"
      "  buf (o17, i17);\n"
      "  not (o18, i18);\n"
      "  // pass_en_switchtype\n"
      "  tranif0 (a19, b19, c19);\n"
      "  tranif1 (a20, b20, c20);\n"
      "  rtranif0 (a21, b21, c21);\n"
      "  rtranif1 (a22, b22, c22);\n"
      "  // pass_switchtype\n"
      "  tran (a23, b23);\n"
      "  rtran (a24, b24);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNand), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kOr), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kXor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kXnor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNot), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTran), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran), nullptr);
}

}  // namespace
