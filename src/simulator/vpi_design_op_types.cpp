#include "lexer/token.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_user.h"

namespace delta {

int VpiBinaryOpType(TokenKind op) {
  switch (op) {
    case TokenKind::kPlus:
      return vpiAddOp;
    case TokenKind::kMinus:
      return vpiSubOp;
    case TokenKind::kStar:
      return vpiMultOp;
    case TokenKind::kSlash:
      return vpiDivOp;
    case TokenKind::kPercent:
      return vpiModOp;
    case TokenKind::kPower:
      return vpiPowerOp;
    case TokenKind::kAmp:
      return vpiBitAndOp;
    case TokenKind::kPipe:
      return vpiBitOrOp;
    case TokenKind::kCaret:
      return vpiBitXorOp;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return vpiBitXnorOp;
    case TokenKind::kAmpAmp:
      return vpiLogAndOp;
    case TokenKind::kPipePipe:
      return vpiLogOrOp;
    case TokenKind::kEqEq:
      return vpiEqOp;
    case TokenKind::kBangEq:
      return vpiNeqOp;
    case TokenKind::kEqEqEq:
      return vpiCaseEqOp;
    case TokenKind::kBangEqEq:
      return vpiCaseNeqOp;
    case TokenKind::kEqEqQuestion:
      return vpiWildEqOp;
    case TokenKind::kBangEqQuestion:
      return vpiWildNeqOp;
    case TokenKind::kLt:
      return vpiLtOp;
    case TokenKind::kGt:
      return vpiGtOp;
    case TokenKind::kLtEq:
      return vpiLeOp;
    case TokenKind::kGtEq:
      return vpiGeOp;
    case TokenKind::kLtLt:
      return vpiLShiftOp;
    case TokenKind::kGtGt:
      return vpiRShiftOp;
    case TokenKind::kLtLtLt:
      return vpiArithLShiftOp;
    case TokenKind::kGtGtGt:
      return vpiArithRShiftOp;
    case TokenKind::kArrow:
      return vpiImplyOp;
    case TokenKind::kKwOr:
      return vpiEventOrOp;
    case TokenKind::kKwIff:
      return vpiIffOp;
    default:
      return 0;
  }
}

int VpiUnaryOpType(TokenKind op) {
  switch (op) {
    case TokenKind::kMinus:
      return vpiMinusOp;
    case TokenKind::kPlus:
      return vpiPlusOp;
    case TokenKind::kBang:
      return vpiNotOp;
    case TokenKind::kTilde:
      return vpiBitNegOp;
    case TokenKind::kAmp:
      return vpiUnaryAndOp;
    case TokenKind::kTildeAmp:
      return vpiUnaryNandOp;
    case TokenKind::kPipe:
      return vpiUnaryOrOp;
    case TokenKind::kTildePipe:
      return vpiUnaryNorOp;
    case TokenKind::kCaret:
      return vpiUnaryXorOp;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return vpiUnaryXNorOp;
    case TokenKind::kKwPosedge:
      return vpiPosedgeOp;
    case TokenKind::kKwNegedge:
      return vpiNegedgeOp;
    default:
      return 0;
  }
}

}  // namespace delta
