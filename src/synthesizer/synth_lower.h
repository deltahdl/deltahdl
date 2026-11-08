#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_pattern.h"

namespace delta {

bool IsCompareOp(TokenKind op);

bool IsShiftOp(TokenKind op);

bool IsUnsignedResultUnaryOp(TokenKind op);

bool IsLogicalOp(TokenKind op);

uint32_t FullAdderBit(AigGraph& aig, uint32_t a, uint32_t b, uint32_t& carry);

struct NonSynthRule {
  std::string_view message;
  std::string_view subclause;
};

NonSynthRule NonSynthExprRule(ExprKind kind);

const Expr* NamedEventTerm(const std::vector<EventExpr>& events,
                           const RtlirModule* mod);

class SynthLower {
 public:
  SynthLower(Arena& arena, DiagEngine& diag);

  AigGraph* Lower(const RtlirModule* mod);

  uint32_t LowerExprBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t LowerInsideRangeMatch(const Expr* sel_expr, const Expr* range,
                                 AigGraph& aig, uint32_t width);

  uint32_t LowerContextOperandBit(const Expr* operand, AigGraph& aig,
                                  uint32_t bit);

  bool CheckStmtSynthesizable(const Stmt* stmt, const RtlirModule* mod);
  bool CheckExprSynthesizable(const Expr* expr);

 private:
  bool CheckElementsSynthesizable(const Expr* expr);

  bool CheckSynthesizable(const RtlirModule* mod);
  bool CheckBlockStmts(const Stmt* stmt, const RtlirModule* mod);
  bool CheckIfSynth(const Stmt* stmt, const RtlirModule* mod);
  bool CheckCaseSynth(const Stmt* stmt, const RtlirModule* mod);
  bool CheckDeclSynthesizable(const Stmt* stmt);
  bool CheckInitializerLowerable(const Expr* expr);
  bool CheckInitializerOperands(const Expr* expr);

  void MapPorts(const RtlirModule* mod, AigGraph& aig);

  NonSynthRule DottedNameRule(const Expr* expr) const;

  void ResetForModule(const RtlirModule* mod);

  void RecordSignal(std::string_view name, uint32_t width, bool is_signed,
                    const RtlirModule* mod);

  void MapParams(const RtlirModule* mod);
  bool MapParam(const RtlirParamDecl& param);
  bool MapParamArray(const RtlirParamDecl& param, ParamStorageShape shape);
  void RecordParamSignal(const RtlirParamDecl& param, ParamStorageShape shape,
                         std::vector<uint32_t> bits);

  bool ReportIfUnloweredParam(const Expr* expr, const Expr* name);

  void MapPortBits(const RtlirPort& port, uint32_t width, AigGraph& aig);

  uint32_t LowerIdentBit(std::string_view name, uint32_t bit);

  uint32_t LowerLiteralBit(const Expr* expr, uint32_t bit);

  const PatternBits& LiteralBits(const Expr* expr);

  uint32_t LowerBinaryBit(const Expr* expr, AigGraph& aig, uint32_t bit);
  uint32_t LowerUnaryBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t LowerAddSubBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  bool ReportArithIfUnlowered(const Expr* expr);

  uint32_t LowerCompareBit(const Expr* expr, AigGraph& aig, uint32_t bit);
  std::optional<bool> TypeRefCompareHere(const Expr* expr) const;

  uint32_t LowerCompareMatch(const Expr* expr, AigGraph& aig);

  uint32_t LowerWildcardMatch(const Expr* expr, AigGraph& aig);

  void ReportWildcardUnlowered(const Expr* expr);

  uint32_t CompareEqual(const Expr* lhs, const Expr* rhs, AigGraph& aig,
                        uint32_t width, bool is_signed);

  uint32_t CompareAtLeast(const Expr* lhs, const Expr* rhs, AigGraph& aig,
                          uint32_t width, bool is_signed);

  uint32_t CompareWidth(const Expr* lhs, const Expr* rhs);

  uint32_t LowerExtendedOperandBit(const Expr* expr, AigGraph& aig,
                                   uint32_t bit, bool sign_extend);

  uint32_t ExtendedOperandWidth(const Expr* expr);

  uint32_t LowerConcatBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t LowerReplicateBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t LowerElementsBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  std::optional<uint32_t> ExprWidth(const Expr* expr);

  std::optional<uint32_t> OperatorWidth(const Expr* expr);

  std::optional<uint32_t> ElementsWidth(const Expr* expr);

  std::optional<uint32_t> ReplicateWidth(const Expr* expr);

  void ReportExprUnlowered(const Expr* expr, std::string_view message,
                           Subclause subclause);

  void ReportUnloweredTarget(const Expr* target);

  uint32_t LowerReductionBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t LowerTruthValue(const Expr* expr, AigGraph& aig,
                           Subclause subclause);

  uint32_t LowerLogicalBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t LowerNegateBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t LowerSelectBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  struct SelectStorage {
    std::string_view name;
    int64_t lo = 0;
    uint32_t count = 0;
  };

  struct ArrayDim {
    int64_t lo = 0;
    uint32_t count = 0;
  };

  struct ArrayShape {
    uint32_t elem_width = 0;
    std::vector<ArrayDim> dims;

    [[nodiscard]] uint32_t Count() const {
      uint32_t n = 1;
      for (const auto& d : dims) n *= d.count;
      return n;
    }
  };

  const ArrayShape* ArrayShapeOf(const Expr* base);

  bool RecordArrayShape(std::string_view name, uint32_t elem_width,
                        uint32_t num_dims,
                        const std::vector<RtlirUnpackedDim>& dims);

  uint32_t ArrayStorageWidth(std::string_view name, uint32_t elem_width);

  enum class ArraySelectKind : uint8_t {
    kNotArray,
    kSlice,
    kElement,
    kInsideElement,
  };

  ArraySelectKind ClassifyArraySelect(const Expr* sel);

  SelectStorage ResolveArraySelect(const Expr* sel);

  uint32_t LowerArraySelectBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  bool LowerArrayTarget(const Expr* lhs, const Expr* rhs, AigGraph& aig);

  SelectStorage ResolveSelect(const Expr* sel);

  bool IsVectorSelect(const Expr* sel);

  void SetGenScope(const GenBlockConsts& consts,
                   const GenBlockPrefixes& prefixes);
  void InstallScopeConstant(std::string_view name, std::vector<uint32_t> bits,
                            bool is_signed, PackedRange range);
  void RestoreShadowedSignals();
  bool RecordBlockParam(const RtlirParamDecl& param);

  uint32_t LowerVariableSelectBit(const Expr* expr, AigGraph& aig,
                                  uint32_t bit);

  uint32_t LowerExprSelectBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t ExprEqualsValue(const Expr* expr, AigGraph& aig, int64_t value);

  int64_t VariableSelectWidth(const Expr* expr);

  int64_t VariableSelectIndex(const Expr* expr, int64_t value, int64_t width,
                              uint32_t bit);

  PackedRange BaseRange(const Expr* base);

  void LowerSelectTarget(const Expr* lhs, const Expr* rhs, AigGraph& aig);

  uint32_t LowerShiftBit(const Expr* expr, AigGraph& aig, uint32_t bit);

  uint32_t ShiftWidth(const Expr* lhs);

  uint32_t LowerAssignRhsBit(const Expr* rhs, AigGraph& aig, uint32_t bit);

  void LowerContAssign(const RtlirContAssign& assign, AigGraph& aig);
  void LowerAlwaysComb(const RtlirProcess& proc, AigGraph& aig);
  void LowerAlwaysFF(const RtlirProcess& proc, AigGraph& aig);
  void LowerAlwaysLatch(const RtlirProcess& proc, AigGraph& aig);

  void LowerStmt(const Stmt* stmt, AigGraph& aig);
  void LowerIfStmt(const Stmt* stmt, AigGraph& aig);
  void LowerCaseStmt(const Stmt* stmt, AigGraph& aig);

  std::optional<uint32_t> CaseCompareWidth(const Stmt* stmt);

  bool IsSignedCase(const Stmt* stmt);
  void LowerAssignStmt(const Stmt* stmt, AigGraph& aig);

  bool LowerIncDecStmt(const Expr* expr, AigGraph& aig);

  void CreateLatches(
      const std::unordered_map<std::string_view, std::vector<uint32_t>>& saved,
      AigGraph& aig);

  void MuxCaseBits(
      std::unordered_map<std::string_view, std::vector<uint32_t>>& result,
      const std::unordered_map<std::string_view, std::vector<uint32_t>>& src,
      uint32_t match, AigGraph& aig);

  void SetSignalBit(std::string_view name, uint32_t bit, uint32_t lit);
  uint32_t GetSignalBit(std::string_view name, uint32_t bit);
  uint32_t SignalWidth(std::string_view name);
  bool IsSignedSignal(std::string_view name);

  bool IsSignedExpr(const Expr* expr);

  void RegisterOutputs(AigGraph& aig);

  Arena& arena_;
  DiagEngine& diag_;

  std::unordered_map<std::string_view, std::vector<uint32_t>> signal_bits_;

  std::unordered_map<std::string_view, uint32_t> signal_widths_;

  std::unordered_map<std::string_view, bool> signal_signed_;

  std::unordered_map<std::string_view, PackedRange> signal_ranges_;

  std::unordered_set<std::string_view> unpacked_arrays_;

  std::unordered_set<std::string_view> unlowered_params_;

  std::vector<const RtlirParamDecl*> block_params_;

  struct ShadowedSignal {
    std::string_view name;
    bool recorded = false;
    bool is_unpacked = false;
    uint32_t width = 0;
    bool is_signed = false;
    PackedRange range;
    std::vector<uint32_t> bits;
  };
  std::vector<ShadowedSignal> shadowed_signals_;

  std::unordered_map<std::string_view, ArrayShape> array_shapes_;

  ScopeMap param_scope_;

  ScopeMap scope_;

  std::vector<std::pair<std::string_view, uint32_t>> output_ports_;

  uint32_t propagated_width_ = 0;

  bool propagated_signed_ = false;

  std::unordered_set<const Expr*> reported_exprs_;

  std::unordered_map<const Expr*, PatternBits> literal_bits_;

  bool lowering_incomplete_ = false;

  const std::vector<TypeRefCompareResult>* type_ref_compares_ = nullptr;
  std::string_view gen_prefix_;
};

}  // namespace delta
