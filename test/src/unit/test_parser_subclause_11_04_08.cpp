#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorParsing, BinaryBitwiseAnd) {
  VerifyInitialRhsOp("module m; initial x = a & b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kAmp);
}

TEST(OperatorParsing, BinaryBitwiseOr) {
  VerifyInitialRhsOp("module m; initial x = a | b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kPipe);
}

TEST(OperatorParsing, BinaryBitwiseXor) {
  VerifyInitialRhsOp("module m; initial x = a ^ b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kCaret);
}

TEST(OperatorParsing, BinaryBitwiseXnor) {
  VerifyInitialRhsOp("module m; initial x = a ^~ b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kCaretTilde);
}

TEST(OperatorParsing, BinaryBitwiseXnorAlt) {
  VerifyInitialRhsOp("module m; initial x = a ~^ b; endmodule\n",
                     ExprKind::kBinary, TokenKind::kTildeCaret);
}

TEST(OperatorParsing, UnaryBitwiseNot) {
  VerifyInitialRhsOp("module m; initial x = ~a; endmodule\n", ExprKind::kUnary,
                     TokenKind::kTilde);
}

}  // namespace
