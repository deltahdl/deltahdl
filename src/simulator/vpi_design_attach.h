#pragma once

namespace delta {

class SimContext;
struct Expr;
struct RtlirDesign;
struct VpiObject;

void AttachDesignToPliApplications(const RtlirDesign* design, SimContext& ctx);

class VpiActiveFrameScope {
 public:
  explicit VpiActiveFrameScope(const Expr* call);
  ~VpiActiveFrameScope();

  VpiActiveFrameScope(const VpiActiveFrameScope&) = delete;
  VpiActiveFrameScope& operator=(const VpiActiveFrameScope&) = delete;

 private:
  const void* thread_ = nullptr;
  VpiObject* outer_ = nullptr;
};

}  // namespace delta
