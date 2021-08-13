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
  - 可变论域_B模型 (Var_B_ab_a.v)

## 哥德尔本体论证明 (GodelGod)
- 哥德尔版：原始版本 (Godel)
  - 公理不一致（固定论域_K） (Inconsistency_Con_K.v)
  - 公理不一致（可变论域_K） (Inconsistency_Var_K.v)
  - 公理不一致（本地_固定论域_KB） (Inconsistency_Local_Con_KB.v)
- 斯科特版：消除了公理不一致的问题 (Scott)
  - 本体论证明与模态坍塌（固定论域_KB） (Scott_Con_KB.v)
- 安德森版：消除了模态坍塌的问题 (Anderson)
  - 本体论证明（固定论域_B） (Anderson_Con_B.v)
  - 可满足性考察（可变论域_B模型） (Satisfiability_Var_B_ab_a.v)
- Hájek版：在安德森版的基础上做了一些改进 (Hajek)
  - 本体论证明（固定论域_KB） (Hajek_Con_KB.v)
- Bjørdal版：使用与安德森不同的方法消除了模态坍塌，且简化了公理系统 (Bjordal)
  - 本体论证明（固定论域_KB） (Bjordal_Con_KB.v)

## 参考
[1] Jordan Howard Sobel. Gödel's ontological proof. On Being and Saying: Essays for Richard Cartwright, 1987: 241–261.  
[2] C.A. Anderson. Some emendations of Godel’s ontological proof. Faith and Philosophy, 1990, 7(3).  
[3] Petr Hájek. Magari and others on Gödel’s ontological proof. 
Logic and algebra, 1996: 125–136.  
[4] Frode Bjørdal. Understanding Gödel's Ontological Argument. The Logica Yearbook 1998, 1999: 214-217.  
[5] C Benzmüller, BW Paleo. Interacting with modal logics in the coq proof assistant. International Computer Science Symposium in Russia, 2015: 398-411.  
[6] Annika Kanckos, BW Paleo. Variants of Gödel's Ontological Proof in a Natural Deduction Calculus. Studia Logica, 2016: 105(3).  
[7] C Benzmüller, L. Weber and BW Paleo. Computer-Assisted Analysis of the Anderson–Hájek Ontological Controversy, Logica Universalis, 2017, 11(1).
