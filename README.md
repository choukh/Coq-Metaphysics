# 计算形而上学

## 逻辑 (Logic)
- 经典逻辑 (Classical.v)
  - 排中律，反证法
- 模态逻辑 (Modal.v)
  - 可能世界语义高阶模态逻辑
  - 全局可证性
  - 固定论域量词
  - 框架条件与层级系统
- 实体及其性质 (Entity.v)
  - 同一性，一致性，严格蕴含
  - 爆炸原理：不一致的性质严格蕴含一切性质
- 本地世界 (LocalWorld.v)
  - 本地可证性
- 可变论域 (VaryingDomain.v)
  - 可变论域量词
- 模型 (Model)
  - 全局_可变论域_S5模型 (G_Var_S5_ab_a.v)

## 哥德尔本体论证明 (GodelGod)
- 哥德尔版：原始版本 (Godel)
  - 公理不一致（全局_固定论域_K系统） (Inconsistency_G_Con_K.v)
- 斯科特版：消除了公理不一致的问题 (Scott)
  - 本体论证明与模态坍塌（全局_固定论域_S5系统） (Scott_G_Con_S5.v)
- 安德森版：消除了模态坍塌的问题 (Anderson)
  - 本体论证明（全局_固定论域_S5系统） (Anderson_G_Con_S5.v)
  - 可满足性考察（全局_可变论域_S5模型） (Satisfiability_G_Var_S5_ab_a.v)

## 参考
- Jordan Howard Sobel. Gödel's ontological proof. On Being and Saying: Essays for Richard Cartwright, 1987: 241–261.
- C.A. Anderson. Some emendations of Godel’s ontological proof. Faith and Philosophy, 1990, 7(3).
- C Benzmüller, BW Paleo. Interacting with modal logics in the coq proof assistant. International Computer Science Symposium in Russia, 2015: 398-411.
- C Benzmüller, BW Paleo. Computer-Assisted Analysis of the Anderson–Hájek Ontological Controversy, Logica Universalis, 2017, 11(1)
