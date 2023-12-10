
(set-logic BV)

(define-fun shr1 ((x (_ BitVec 64))) (_ BitVec 64) (bvlshr x #x0000000000000001))
(define-fun shr4 ((x (_ BitVec 64))) (_ BitVec 64) (bvlshr x #x0000000000000004))
(define-fun shr16 ((x (_ BitVec 64))) (_ BitVec 64) (bvlshr x #x0000000000000010))
(define-fun shl1 ((x (_ BitVec 64))) (_ BitVec 64) (bvshl x #x0000000000000001))
(define-fun if0 ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64))) (_ BitVec 64) (ite (= x #x0000000000000001) y z))

(synth-fun f ( (x (_ BitVec 64))) (_ BitVec 64)
(

(Start (_ BitVec 64) (#x0000000000000000 #x0000000000000001 x (bvnot Start)
                    (shl1 Start)
 		    (shr1 Start)
		    (shr4 Start)
		    (shr16 Start)
		    (bvand Start Start)
		    (bvor Start Start)
		    (bvxor Start Start)
		    (bvadd Start Start)
		    (if0 Start Start Start)
 ))
)
)


(constraint (= (f #xaaba0a1e513ddb98) #xffd1e1a50c466d37))
(constraint (= (f #x5ba8b3e64149879d) #xa4574c19beb67862))
(constraint (= (f #xe3aa17442e4b0144) #x5501ba33751efc33))
(constraint (= (f #xd61ee2eb88a4662e) #x7da3573d6612cd75))
(constraint (= (f #x7796419c3da60c73) #x8869be63c259f38c))
(constraint (= (f #x767407470847eca9) #x898bf8b8f7b81356))
(constraint (= (f #x8bc9401a15d1b621) #x7436bfe5ea2e49de))
(constraint (= (f #x0398d7d37d9a4ee7) #xfc67282c8265b118))
(constraint (= (f #x01e9ec219ea96b45) #xfe1613de615694ba))
(constraint (= (f #x5007bdabd96c965c) #x0fe8c6fc73ba3ceb))
(constraint (= (f #x81c15aa2e69e345e) #x7abbf0174c2562e5))
(constraint (= (f #xa5d626d567537d92) #x0e7d8b7fca058749))
(constraint (= (f #x96418c5a04a2658c) #x3d3b5af1f218cf5b))
(constraint (= (f #xddb4c3b6da16c81e) #x66e1b4db71bba7a5))
(constraint (= (f #xd223a6c6ae4d9c39) #x2ddc593951b263c6))
(constraint (= (f #xdb545019b1d3e69e) #x6e030fb2ea844c25))
(constraint (= (f #x7bd20d4c5137a6b8) #x8c89d81b0c590bd7))
(constraint (= (f #x14c520e8eb190720) #xc1b09d453eb4ea9f))
(constraint (= (f #x98882cb2be78d9d4) #x366779e7c4957283))
(constraint (= (f #x6c4b9e04cdabec0a) #xbb1d25f196fc3be1))
(constraint (= (f #xd605a5387eb6084c) #x7def105683dde71b))
(constraint (= (f #xec2b6d4a047682e1) #x13d492b5fb897d1e))
(constraint (= (f #x76d41a42e40161ed) #x892be5bd1bfe9e12))
(constraint (= (f #x3d01258536a2453c) #x48fc8f705c19304b))
(constraint (= (f #x79b3d2219eeda23b) #x864c2dde61125dc4))
(constraint (= (f #xe2dc75192de575bc) #x576aa0b4764f9ecb))
(constraint (= (f #x2add49c27265e4e0) #x7f6822b8a8ce515f))
(constraint (= (f #x81267a5b27e1dabe) #x7c8c90ee885a6fc5))
(constraint (= (f #xe96c88e60b62a338) #x43ba654dddd81657))
(constraint (= (f #x5719be0772de734d) #xa8e641f88d218cb2))
(constraint (= (f #x76022a8a81d08a9e) #x9df980607a8e6025))
(constraint (= (f #x759cd2ad8865e9a5) #x8a632d52779a165a))
(constraint (= (f #x6de46bc7de288ea9) #x921b943821d77156))
(constraint (= (f #xd5d13ea4e1523451) #x2a2ec15b1eadcbae))
(constraint (= (f #x4d33c7220b1ba54b) #xb2cc38ddf4e45ab4))
(constraint (= (f #x0a18cdc099b7eab0) #xe1b596be32d83fef))
(constraint (= (f #x01176e872a218b6e) #xfcb9b46a819b5db5))
(constraint (= (f #x0000732a500e1011) #xffff8cd5aff1efee))
(constraint (= (f #x86b4d9954b05e1ec) #x6be173401eee5a3b))
(constraint (= (f #xb82502ec0b286d3e) #xd790f73bde86b845))
(constraint (= (f #x86c2d0d0665c6741) #x793d2f2f99a398be))
(constraint (= (f #x573c87c1442d8a27) #xa8c3783ebbd275d8))
(constraint (= (f #x2eda3267e33d1e58) #x737168c85648a4f7))
(constraint (= (f #xea4714ab66c8ec51) #x15b8eb54993713ae))
(constraint (= (f #xb907458844412033) #x46f8ba77bbbedfcc))
(constraint (= (f #xeecc11367122939a) #x339bcc5cac984531))
(constraint (= (f #xdaee63ae50b0062e) #x6f34d4f50defed75))
(constraint (= (f #xbed2a89ebe0ceb71) #x412d576141f3148e))
(constraint (= (f #x56e27734d873696d) #xa91d88cb278c9692))
(constraint (= (f #xacde9de066934c96) #xf964265ecc461a3d))
(constraint (= (f #x3a5a100032c4a0ae) #x50f1cfff67b21df5))
(constraint (= (f #x737328de17c7a111) #x8c8cd721e8385eee))
(constraint (= (f #xea462be8eab4c7e7) #x15b9d417154b3818))
(constraint (= (f #x213be633c9bb24b5) #xdec419cc3644db4a))
(constraint (= (f #xa7aaa7cc51246e52) #x0900089b0c92b509))
(constraint (= (f #x0d5678aa3dacebe6) #xd7fc960146f93c4d))
(constraint (= (f #xd907669014886b29) #x26f8996feb7794d6))
(constraint (= (f #x6da5376c803335ce) #xb71059ba7f665e95))
(constraint (= (f #x4bedee7e31b043e5) #xb4121181ce4fbc1a))
(constraint (= (f #xe2b1647a88c71cb0) #x57ebd29065aaa9ef))
(constraint (= (f #x66dcaabe7cd82086) #xcb69ffc489779e6d))
(constraint (= (f #x06241e834059c721) #xf9dbe17cbfa638de))
(constraint (= (f #x67118033480dce61) #x98ee7fccb7f2319e))
(constraint (= (f #xb4cdc932275dced9) #x4b3236cdd8a23126))
(constraint (= (f #xa2673e9ebe7cb999) #x5d98c16141834666))
(constraint (= (f #x98be8dee5556b438) #x35c45634fffbe357))
(constraint (= (f #xd68381e4a02eca7c) #x7c757a521f73a08b))
(constraint (= (f #x3123cc513d246433) #xcedc33aec2db9bcc))
(constraint (= (f #x458950423a44d3e3) #xba76afbdc5bb2c1c))
(constraint (= (f #xe43ecd7ee8e97e80) #x534397834543847f))
(constraint (= (f #x68c0ee836a39454a) #xc5bd3475c1543021))
(constraint (= (f #x98ea488465d3d437) #x6715b77b9a2c2bc8))
(constraint (= (f #x4d38ce4ee28c4124) #x18559513585b3c93))
(constraint (= (f #xa7e6a3492e21e6dd) #x58195cb6d1de1922))
(constraint (= (f #x7ba73434b392c47a) #x8d0a6361e547b291))
(constraint (= (f #x22558019d55a41ee) #x98ff7fb27ff13a35))
(constraint (= (f #x1e4e6ddcee9400a8) #xa514b6693443fe07))
(constraint (= (f #x4c6b96c4e6eddb62) #x1abd3bb14b366dd9))
(constraint (= (f #x5e73d9e8e35534a0) #xe4a472455600621f))
(constraint (= (f #xba26932e03e736e7) #x45d96cd1fc18c918))
(constraint (= (f #xbeaa1999747ae1e3) #x4155e6668b851e1c))
(constraint (= (f #x0bde9bb3b5624999) #xf421644c4a9db666))
(constraint (= (f #xead1c88eb53abde6) #x3f8aa653e04fc64d))
(constraint (= (f #xe72253b977959604) #x4a9904d3993f3df3))
(constraint (= (f #x501ee844c761be01) #xafe117bb389e41fe))
(constraint (= (f #x3c208549843e25c1) #xc3df7ab67bc1da3e))
(constraint (= (f #xd8eb774e850ee728) #x753d9a1470d34a87))
(constraint (= (f #xa4b9305ea8e54038) #x11d46ee405503f57))
(constraint (= (f #x3c2d688d7acb790e) #x4b77c6578f9d94d5))
(constraint (= (f #xd9c75760794bc868) #x72a9f9de941ca6c7))
(constraint (= (f #x394e1b5ed3895c3b) #xc6b1e4a12c76a3c4))
(constraint (= (f #x7e6cd2a95698c581) #x81932d56a9673a7e))
(constraint (= (f #xcded8264ae0e618d) #x32127d9b51f19e72))
(constraint (= (f #x58ada189bbb1819c) #xf5f71b62cceb7b2b))
(constraint (= (f #x8ec48b7bd8aea6ec) #x53b25d8c75f40b3b))
(constraint (= (f #xd86e83058713e160) #x76b476ef6ac45bdf))
(constraint (= (f #xcd166ddb05daba75) #x32e99224fa25458a))
(constraint (= (f #x9e5dd6108a06b024) #x24e67dce61ebef93))
(constraint (= (f #xbb2acd9c1924416e) #xce7f972bb4933bb5))
(constraint (= (f #x735d9eedecd85b11) #x8ca261121327a4ee))
(check-synth)
