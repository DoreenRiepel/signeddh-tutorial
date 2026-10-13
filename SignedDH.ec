require import AllCore Real FMap FSet Distr.
require import PROM.

require (*--*) StdOrder.
(*---*) import StdOrder.RealOrder.

require (*--*) St_CDH_abstract SUFCMA UAKE.

(** Buckle Up! **)
(* Starting notes:
   - We (try to) follow Doreen and Paul's model as closely as possible
     while remaining precise.
   - The NIKE is split out as Nominal Group with Gap-DH + RO. The
     entire scheme could be proved assuming an abstract NIKE (with
     m-CKS-heavy security), and that be constructed from NG + Gap-DH +
     RO.
*)

(** Types and operators for the DH group **)
type pdh, sdh, sskey.

op g: pdh.
op [lossless] dsk: sdh distr.
op (^): pdh -> sdh -> pdh.

axiom shared_keyC x y:
     x \in dsk
  => y \in dsk
  => (g ^ x) ^ y = (g ^ y) ^ x.

axiom public_key_injective x x':
  g ^ x = g ^ x' => x = x'.

op [lossless full uniform] dssk: sskey distr.

(** Instantiate the GapDH theory **)
clone import St_CDH_abstract as StCDH with
  type pkey <= pdh,
  type skey <= sdh,
  op   g    <= g,
  op   dsk  <= dsk,
  op   (^)  <= (^)
proof *.
realize dsk_ll by exact: dsk_ll.
realize shared_keyC by exact: shared_keyC.
realize public_key_injective by exact: public_key_injective. 

(** Additional types for the signature scheme **)
type pkey, skey, sig.

(** Instantiate the UFCMA theory **)
clone import SUFCMA as Signature with
  type pkey   <= pkey,
  type skey   <= skey,
  type sig    <= sig,
  type msg    <= pdh * pdh
proof *.

(** Additional types for defining protocols,
    plus RO instantiation
**)
type client_state = { pk: pkey;     (* The server's identity, as its public key *)
                      epk: pdh;     (* The client's ephemeral public key *)
                      esk: sdh   }. (* The client's ephemeral secret *)

clone import FullRO as H with
  type in_t    <= pdh * pdh * pdh,
  type out_t   <= sskey,
  op   dout  _ <= dssk,
  type d_in_t  <= unit,
  type d_out_t <= bool
proof *.

(** Instantiate the ProtRO theory **)
clone import UAKE as Security with
  type pkey         <= pkey,
  type skey         <= skey,
  type sskey        <= sskey,
  op   dssk         <= dssk,
  type client_state <= client_state,
  type msg1         <= pdh,
  type msg2         <= pdh * sig,
  type ro_in        <= pdh * pdh * pdh,
  type ro_out       <= sskey,
  op   d_ro         <= Self.dssk
proof *.
realize dssk_ll by exact: dssk_ll.
realize dssk_uni by exact: dssk_uni.
realize dssk_fu by exact: dssk_fu.

(** Finally, we define the signed DH protocol **)
module SignedDH (S : SigScheme) (H : RO) : UAKE = {
  proc gen() = {
    var kp;

    kp <@ S.keygen();
    return kp;
  }

  proc init(pk) = {
    var x_sk;

    x_sk <$ dsk;
    return ({| pk = pk; epk = g ^ x_sk; esk = x_sk |}, g ^ x_sk);
  }

  proc resp(sk_s, x_pk) = {
    var y_sk, s, ks;

    y_sk <$ dsk;
    s <@ S.sign(sk_s, (x_pk, g ^ y_sk));
    ks <@ H.get(x_pk ^ y_sk, x_pk, g ^ y_sk);
    return (ks, (g ^ y_sk, s));
  }

  proc recv(st, c) = {
    var y_pk, s, b, kc;
    var r <- None;

    (y_pk, s) <- c;
    b <- verify(st.`pk, (st.`epk,  y_pk), s);
    if (b) {
      kc <@ H.get(y_pk ^ st.`esk, st.`epk, y_pk);
      r <- Some kc;
    }
    return r;
  }
}.


(* Reductions B1 and B2 start here *)

(* Reduction B1 *)
(* B1 silences all oracle activity after the first forgery capture.
   m_sig counts every native key generation; sig_idx translates accepted
   local server handles for signing, corruption, and the returned forgery.
   Generation checks earlier unregistered clients, as Game3 does.
   Init also carries the preceding client-share collision filter. *)

module B1 (S : SigScheme) (A : Adv_UAKE_RO) (O : CMA_Oracles) = {
  var b_ror : bool

  var forgery : (int * (pdh * pdh) * sig) option

  var resp_inputs : pdh fset
  var bad_2 : bool

  var n : int
  var m : int
  var m_sig : int
  var sig_idx : (int, int) fmap

  var p_map : (int, int) fmap
  var i_map : (int, pdh) fmap
  var r_map : (int option * int, (pdh * sig) fset) fmap

  var pk_map : (int, pkey) fmap
  var c_map : (int, client_state) fmap

  var q : int fset
  var ich : int fset
  var rch : int fset
  var xp : int fset
  var cr : int fset

  module Oracles = {
    proc gen(): pkey = {
      var pk;

      pk <- witness;
      if (forgery = None) {
        m_sig <- m_sig + 1;
        pk <@ O.gen();
        if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
          pk <- witness;
        } else {
          m <- m + 1;
          pk_map.[m] <- pk;
          sig_idx.[m] <- m_sig;
        }
      }
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (forgery = None) {
        if (0 < j <= m) {
          cr <- cr `|` fset1 j;
          r <@ O.corrupt(oget sig_idx.[j]);
        }
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (forgery = None) {
        if (0 < i <= n /\ i \notin ich) {
          xp <- xp `|` fset1 i;
          r <- c_map.[i];
        }
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var jo, x, c;

      c <- witness;
      if (forgery = None) {
        x <$ dsk;
        c <- g ^ x;
        if (has (fun _ st=> st.`epk = c) c_map \/ c \in resp_inputs) {
          bad_2 <- true;
          c <- witness;
        } else {
          n <- n + 1;
          c_map.[n] <- {| pk = pk; epk = c; esk = x |};
          jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
          if (jo is Some j) {
            p_map.[n] <- j;
            i_map.[n] <- c;
          }
        }
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, h, y, sig;
      var r <- None;

      if (forgery = None) {
        if (0 < j <= m) {
          resp_inputs <- resp_inputs `|` fset1 c;
          y <$ dsk;
          h <- g ^ y;
          sig <@ O.sign(oget sig_idx.[j], (c, h));
          c' <- (h, oget sig);
          k <@ RO.get(c ^ y, c, h);
          io <- find (fun i j' => j' = j /\ i_map.[i] = Some c) p_map;
          if (io is Some i) {
            r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
            if (ch /\ i \notin xp) {
              if (b_ror) { k <$ dssk; }
              ich <- ich `|` fset1 i;
            }
          }
          r <- Some (k, c');
        }
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (forgery = None) {
        if (0 < i <= n /\ i \notin q) {
          st_i <- oget c_map.[i];
          q <- q `|` fset1 i;

          if (c \notin odflt fset0 r_map.[p_map.[i], i] /\
              !(i \in ich /\ p_map.[i] <> None /\ oget p_map.[i] \in cr)) {
            (h, sig) <- c;
            b <- verify(st_i.`pk, (st_i.`epk, h), sig);
            if (b) {
              k <@ RO.get(h ^ st_i.`esk, st_i.`epk, h);
              ko <- Some k;
            }
            if ((i \in ich \/ ch)
                /\ i \notin xp
                /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
                /\ ko <> None) {
              if (forgery = None) {
                forgery <- Some (oget sig_idx.[oget p_map.[i]], (st_i.`epk, h), sig);
              }
              if (ch /\ b_ror) { k <$ dssk; ko <- Some k; }
              ich <- ich `|` fset1 i;
            }
          }
        }
      }
      return ko;
    }

    proc h(z: pdh, x: pdh, y: pdh): sskey = {
      var k <- witness;
      if (forgery = None) {
        k <@ RO.get(z, x, y);
      }
      return k;
    }
  }

  proc forge() = {
    var b';

    forgery <- None;
    RO.init();
    p_map <- empty;


    i_map <- empty;
    m <- 0;
    m_sig <- 0;
    sig_idx <- empty;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    c_map <- empty;
    bad_2 <- false;


    b' <@ A(Oracles).distinguish();
    return oget forgery;
  }
}.


module B1_0 (S : SigScheme) (A : Adv_UAKE_RO) (O : CMA_Oracles) = {
  proc forge() = {
    var f;

    B1.b_ror <- false;
    f <@ B1(S, A, O).forge();
    return f;
  }
}.

module B1_1 (S : SigScheme) (A : Adv_UAKE_RO) (O : CMA_Oracles) = {
  proc forge() = {
    var f;

    B1.b_ror <- true;
    f <@ B1(S, A, O).forge();
    return f;
  }
}.


(* Reduction B2 *)
(* B2 simulates the games below after collisions have been handled. 
   n_x counts every gen_1 call while n counts only accepted sessions; x_idx retains mapping for Expose *)

module B2 (S : SigScheme) (A : Adv_UAKE_RO) (O : St_CDH_Oracles) = {
  include var Exp_b(SignedDH(S), RO, A) [-run]

  var resp_inputs : pdh fset
  var bad_2 : bool
  var h_map : (pdh option * pdh * pdh, sskey) fmap
  var bad_1 : bool
  var bad_3 : bool
  var n_x : int
  var x_idx : (int, int) fmap 
  var bad_4 : bool

  module Oracles = {
    proc h'(x, y) = {
      var k;

      if ((None, x, y) \notin h_map) {
        k <$ dssk;
        h_map.[None, x, y] <- k;
      }
      return oget h_map.[None, x, y];
    }

    proc h(z, x, y) = {
      var k, ko, b;

      ko <- None;
      if ((Some z, x, y) \notin h_map) {
        b <@ O.ddh(x, y, z);
        if (has (fun _ st=> st.`epk = x) c_map /\ b) { 
          k <@ h'(x, y);
          ko <- Some k;
        } else {
          k <$ dssk;
          h_map.[Some z, x, y] <- k;
          ko <- Some k;
        }
      } else {
        ko <- h_map.[Some z, x, y];
      }
      return oget ko;
    }

    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true; 
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }

      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        cr <- cr `|` fset1 j;
        r <- sk_map.[j];
      }
      return r;
    }

    proc expose(i) = {
      var pk, x;
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        if (c_map.[i] <> None) {
          pk <- (oget c_map.[i]).`pk;
          x <@ O.corrupt_1(oget x_idx.[i]);
          r <- Some {| pk = pk; epk = g ^ oget x; esk = oget x |};
        }
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var jo, c;

      n_x <- n_x + 1;
      c <@ O.gen_1();
      if (has (fun _ st=> st.`epk = c) c_map \/ c \in resp_inputs) {
        bad_2 <- true;
        c <- witness;
      } else {
        if (has (fun (zxy : pdh option * pdh * pdh) _=> zxy.`1 <> None /\ zxy.`2 = c) h_map) {
          bad_4 <- true;
          c <- witness;
        } else {
          n <- n + 1;
          x_idx.[n] <- n_x;
          c_map.[n] <- {| pk = pk; epk = c; esk = witness |};
          jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
          if (jo is Some j) {
            p_map.[n] <- j;
            i_map.[n] <- c;
          }
        }
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        resp_inputs <- resp_inputs `|` fset1 c;
        y <- witness; (* silence a warning: all paths that use y define it first *)
        if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) {
          h <@ O.gen_2();
        } else {
          y <$ dsk;
          h <- g ^ y;
        }
        if (has (fun (zxy : pdh option * pdh * pdh) _=> zxy.`2 = c /\ zxy.`3 = h) h_map) {
          bad_4 <- true;
        } else {
          sk_j <- oget sk_map.[j];
          sig <@ S.sign(sk_j, (c, h));
          c' <- (h, sig);
          if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) {
            k <@ h'(c, h);
          } else {
            k <@ h(c ^ y, c, h);
          }
          io <- find (fun i j' => j' = j /\ i_map.[i] = Some c) p_map;
          if (io is Some i) {
            r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
            if (ch /\ i \notin xp) {
              ich <- ich `|` fset1 i;
            }
          }
          r <- Some (k, c');
        }
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;

        if (c \notin odflt fset0 r_map.[p_map.[i], i] /\ 
            !(i \in ich /\ p_map.[i] <> None /\ oget p_map.[i] \in cr)) { 
          (h, sig) <- c;
          b <- verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ h'(st_i.`epk, h);
            ko <- Some k;
          }
          if ((i \in ich \/ ch)
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_3 <- true;
            ko <- None;
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

  }

  proc solve() = {
    var b';

    b_ror <- witness;
    RO.init();
    h_map <- empty;
    p_map <- empty;
    i_map <- empty;


    m <- 0;
    n <- 0;
    n_x <- 0;
    x_idx <- empty;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;
    bad_4 <- false;

    b' <@ A(Oracles).distinguish();
  }
}.

(* Reductions B1 and B2 end here *)


section.
declare module S <: SigScheme { -Exp_b, -SUFCMA, -RO, -B1, -B2, -St_CDH }. (* STATE ISOLATION added by GPT-6.1-Sol: forbid signature code from directly accessing the CDH experiment state. *)
declare module A <: Adv_UAKE_RO { -Exp_b, -SUFCMA, -RO, -B1, -B2, -S, -St_CDH }. (* STATE ISOLATION added by GPT-6.1-So: forbid adversary access to CDH state; retain the supplied oracle interface. *)


(* Games G0-G4 start here *)

local module Game0_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]

  module Oracles = {
    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      m <- m + 1;
      pk_map.[m] <- pk;
      sk_map.[m] <- sk;
      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        cr <- cr `|` fset1 j;
        r <- sk_map.[j];
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var jo, x, c;

      x <$ dsk;
      c <- g ^ x;
      n <- n + 1;
      c_map.[n] <- {| pk = pk; epk = c; esk = x |};
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        y <$ dsk;
        h <- g ^ y;
        sk_j <- oget sk_map.[j];
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(c ^ y, c, h);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;

        if (c \notin odflt fset0 r_map.[p_map.[i], i] /\ 
            !(i \in ich /\ p_map.[i] <> None /\ oget p_map.[i] \in cr)) { 
          (h, sig) <- c;
          b <- verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(h ^ st_i.`esk, st_i.`epk, h);
            ko <- Some k;
          }
          if (   ch
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            if (b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

    proc h = RO.get
  }

  proc run(b) = {
    var b';

    b_ror <- b;
    RO.init();


    p_map <- empty;
    i_map <- empty;
    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.


local module Game1_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]

  var bad_1: bool

  module Oracles = {
    include Game0_b.Oracles [-gen]

    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        (* Pen and paper says "Stop" *)
        (* Here, we don't stop; we just don't actually register the key and move on *)
        (* The only thing we care about is the rest of the proof,
           where we want to rely on the fact that each client instance
           has at most one intended honest partner
        *)
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }

      return pk;
    }
  }

  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    p_map <- empty;


    i_map <- empty;
    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.


local module Game2_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]
  var resp_inputs : pdh fset
  var bad_2 : bool

  module Oracles = {
    include Game1_b.Oracles [-init, respond]
    proc init(pk: pkey): pdh = {
      var jo, x, c;

      x <$ dsk;
      c <- g ^ x;
      if (has (fun _ st=> st.`epk = c) c_map \/ c \in resp_inputs) {
        bad_2 <- true;
        c <- witness;
      } else {
        n <- n + 1;
        c_map.[n] <- {| pk = pk; epk = c; esk = x |};
        jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
        if (jo is Some j) {
          p_map.[n] <- j;
          i_map.[n] <- c;
        }
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        resp_inputs <- resp_inputs `|` fset1 c;
        y <$ dsk;
        h <- g ^ y;
        sk_j <- oget sk_map.[j];
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(c ^ y, c, h);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }
  }
  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    p_map <- empty;


    i_map <- empty;
    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.


local module Game3_b = {
  include var Game1_b [-run]
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game2_b [-run]

  var bad_3 : bool

  module Oracles = {
    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        (* Here, we don't stop; we just don't actually register the key and move on *)
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }

      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        cr <- cr `|` fset1 j;
        r <- sk_map.[j];
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var jo, x, c;

      x <$ dsk;
      c <- g ^ x;
      if (has (fun _ st=> st.`epk = c) c_map \/ c \in resp_inputs) {
        bad_2 <- true;
        c <- witness;
      } else {
        n <- n + 1;
        c_map.[n] <- {| pk = pk; epk = c; esk = x |};
        jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
        if (jo is Some j) {
          p_map.[n] <- j;
          i_map.[n] <- c;
        }
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        resp_inputs <- resp_inputs `|` fset1 c;
        y <$ dsk;
        h <- g ^ y;
        sk_j <- oget sk_map.[j];
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        k <@ RO.get(c ^ y, c, h);
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          (*** Instead of initialising all of r_map to output the
          empty set, we read undefined entries as the empty set
          here. ***)
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;

        if (c \notin odflt fset0 r_map.[p_map.[i], i] /\ 
            !(i \in ich /\ p_map.[i] <> None /\ oget p_map.[i] \in cr)) { 
          (h, sig) <- c;
          b <- verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(h ^ st_i.`esk, st_i.`epk, h);
            ko <- Some k;
          }
          if ((i \in ich \/ ch)
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_3 <- true;
            ko <- None;
            ich <- ich `|` fset1 i; 
          }
        }
      }
      return ko;
    }

    proc h = RO.get
  }

  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    p_map <- empty;

    i_map <- empty;
    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.


local module Game4_b = {
  include var Game1_b [-run]
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game2_b [-run]
  include var Game3_b [-run]

  var h_map : (pdh option * pdh * pdh, sskey) fmap
  var bad_4 : bool 

  module Oracles = {
    proc h'(x, y) = {
      var k;

      if ((None, x, y) \notin h_map) {
        k <$ dssk;
        h_map.[None, x, y] <- k;
      }
      return oget h_map.[None, x, y];
    }

    proc h(z, x, y) = {
      var io, st_i, k, ko;

      ko <- None;
      if ((Some z, x, y) \notin h_map) {
        io <- find (fun _ st=> st.`epk = x) c_map; 
        if (io is Some i) {
          st_i <- oget c_map.[i];
          if (z = y ^ st_i.`esk) {
            k <@ h'(x, y);
            ko <- Some k;
          }
        }
        if (ko = None) { 
          k <$ dssk;
          h_map.[Some z, x, y] <- k;
          ko <- Some k;
        }
      } else {
        ko <- h_map.[Some z, x, y];
      }
      return oget ko;
    }

    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        (* Here, we don't stop; we just don't actually register the key and move on *)
        pk <- witness;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }

      return pk;
    }

    proc corrupt(j: int): skey option = {
      var r <- None;

      if (0 < j <= m) {
        cr <- cr `|` fset1 j;
        r <- sk_map.[j];
      }
      return r;
    }

    proc expose(i) = {
      var r <- None;

      if (0 < i <= n /\ i \notin ich) {
        xp <- xp `|` fset1 i;
        r <- c_map.[i];
      }
      return r;
    }

    proc init(pk: pkey): pdh = {
      var jo, x, c;

      x <$ dsk;
      c <- g ^ x;
      if (has (fun _ st=> st.`epk = c) c_map \/ c \in resp_inputs) {
        bad_2 <- true;
        c <- witness;
      } else {
        if (has (fun (zxy : pdh option * pdh * pdh) _=> zxy.`1 <> None /\ zxy.`2 = c) h_map) { 
          bad_4 <- true; 
          c <- witness; 
        } else { 
          n <- n + 1; 
          c_map.[n] <- {| pk = pk; epk = c; esk = x |}; 
          jo <- find (fun _ pk_j=> pk_j = pk) pk_map; 
          if (jo is Some j) { 
            p_map.[n] <- j; 
            i_map.[n] <- c; 
          } 
        } 
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        resp_inputs <- resp_inputs `|` fset1 c;
        y <$ dsk;
        h <- g ^ y;
        if (has (fun (zxy : pdh option * pdh * pdh) _=> zxy.`2 = c /\ zxy.`3 = h) h_map) { 
          bad_4 <- true; 
        } else { 
          sk_j <- oget sk_map.[j]; 
          sig <@ S.sign(sk_j, (c, h)); 
          c' <- (h, sig); 
          if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) { 
            k <@ h'(c, h);
          } else { 
            k <@ h(c ^ y, c, h); 
          } 
          io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map; 
          if (io is Some i) { 
            r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c'; 
            if (ch /\ i \notin xp) { 
              if (b_ror) { k <$ dssk; } 
              ich <- ich `|` fset1 i; 
            } 
          } 
          r <- Some (k, c'); 
        } 
      }
      return r;
    }

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;

        if (c \notin odflt fset0 r_map.[p_map.[i], i] /\ 
            !(i \in ich /\ p_map.[i] <> None /\ oget p_map.[i] \in cr)) { 
          (h, sig) <- c;
          b <- verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ h'(st_i.`epk, h);
            ko <- Some k;
          }
          if ((i \in ich \/ ch)
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_3 <- true;
            ko <- None;
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

  }

  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    h_map <- empty;


    p_map <- empty;
    i_map <- empty;
    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;
    bad_4 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

(* Games G0-G4 end here *)




(* Intermediate games G05-G35 start here *)
(* Flag-only half-step games introduce the next bad flag
   while retaining the preceding game's answers. They reuse the
   whole-numbered game declarations above. *)

local module Game05_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]

  module Oracles = {

    include Game1_b.Oracles [-gen]

    proc gen(): pkey = {
      var pk, sk;

      (pk, sk) <@ S.keygen();
      if (has (fun i st=> st.`pk = pk /\ p_map.[i] = None) c_map) {
        bad_1 <- true;
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      } else {
        m <- m + 1;
        pk_map.[m] <- pk;
        sk_map.[m] <- sk;
      }

      return pk;
    }
  }

  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    p_map <- empty;
    i_map <- empty;


    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

local module Game15_b = {
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]
  include var Game2_b [-run]

  module Oracles = {
    include Game2_b.Oracles [-init]
    proc init(pk: pkey): pdh = {
      var jo, x, c;

      x <$ dsk;
      c <- g ^ x;
      if (has (fun _ st=> st.`epk = c) c_map \/ c \in resp_inputs) {
        bad_2 <- true;
      }
      n <- n + 1;
      c_map.[n] <- {| pk = pk; epk = c; esk = x |};
      jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
      if (jo is Some j) {
        p_map.[n] <- j;
        i_map.[n] <- c;
      }
      return c;
    }
  }
  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    p_map <- empty;

    i_map <- empty;
    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;

    bad_1 <- false;
    bad_2 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

local module Game25_b = {
  include var Game1_b [-run]
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game2_b [-run]
  include var Game3_b [-run]

  module Oracles = {
    include Game2_b.Oracles [-receive] 

    proc receive(i: int, c: pdh * sig, ch: bool): sskey option = {
      var st_i, k, h, sig, b;
      var ko <- None;

      if (0 < i <= n /\ i \notin q) {
        st_i <- oget c_map.[i];
        q <- q `|` fset1 i;

        if (c \notin odflt fset0 r_map.[p_map.[i], i] /\ 
            !(i \in ich /\ p_map.[i] <> None /\ oget p_map.[i] \in cr)) { 
          (h, sig) <- c;
          b <- verify(st_i.`pk, (st_i.`epk, h), sig);
          if (b) {
            k <@ RO.get(h ^ st_i.`esk, st_i.`epk, h); 
            ko <- Some k;
          }

          if ((i \in ich \/ ch)
              /\ i \notin xp
              /\ p_map.[i] <> None /\ 0 < oget p_map.[i] <= m /\ oget p_map.[i] \notin cr
              /\ ko <> None) {
            bad_3 <- true;
            if (ch /\ b_ror) { k <$ dssk; ko <- Some k; }
            ich <- ich `|` fset1 i;
          }
        }
      }
      return ko;
    }

  }

  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    p_map <- empty;
    i_map <- empty;


    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;
    bad_1 <- false;

    bad_2 <- false;
    bad_3 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.


local module Game35_b = {
  include var Game2_b [-run]
  include var Game3_b [-run]
  include var Exp_b(SignedDH(S), RO, A) [-run]
  include var Game1_b [-run]
  include var Game4_b [-run] 

  module Oracles = {
    include Game3_b.Oracles [-init, respond, h] 

    proc h(z: pdh, x: pdh, y: pdh): sskey = {
      var io, st_i, k;
      var valid_dh <- false;

      k <@ RO.get(z, x, y); 
      if ((Some z, x, y) \notin h_map) {
        io <- find (fun _ st=> st.`epk = x) c_map; 
        if (io is Some i) {
          st_i <- oget c_map.[i];
          valid_dh <- z = y ^ st_i.`esk;
        }
        if (!valid_dh) {
          h_map.[Some z, x, y] <- k;
        }
      }
      return k; 
    }

    proc init(pk: pkey): pdh = {
      var jo, x, c;

      x <$ dsk;
      c <- g ^ x;
      if (has (fun _ st=> st.`epk = c) c_map \/ c \in resp_inputs) {
        bad_2 <- true;
        c <- witness;
      } else {
        n <- n + 1;
        if (has (fun (zxy : pdh option * pdh * pdh) _=> zxy.`1 <> None /\ zxy.`2 = c) h_map) {
          bad_4 <- true; 
        }
        c_map.[n] <- {| pk = pk; epk = c; esk = x |};
        jo <- find (fun _ pk_j=> pk_j = pk) pk_map;
        if (jo is Some j) {
          p_map.[n] <- j;
          i_map.[n] <- c;
        }
      }
      return c;
    }

    proc respond(j: int, c: pdh, ch: bool): (sskey * (pdh * sig)) option = {
      var k, c', io, sk_j, h, y, sig;
      var r <- None;

      if (0 < j <= m) {
        resp_inputs <- resp_inputs `|` fset1 c;
        y <$ dsk;
        h <- g ^ y;
        if (has (fun (zxy : pdh * pdh * pdh) _=> zxy.`2 = c /\ zxy.`3 = h) RO.m) {
          bad_4 <- true; 
        }
        sk_j <- oget sk_map.[j];
        sig <@ S.sign(sk_j, (c, h));
        c' <- (h, sig);
        if (has (fun i j' => j' = j /\ i_map.[i] = Some c) p_map) {
          k <@ RO.get(c ^ y, c, h); 
        } else {
          k <@ h(c ^ y, c, h);
        }
        io <- find (fun i _=> p_map.[i] = Some j /\ i_map.[i] = Some c) c_map;
        if (io is Some i) {
          r_map.[Some j, i] <- (odflt fset0 r_map.[Some j, i]) `|` fset1 c';
          if (ch /\ i \notin xp) {
            if (b_ror) { k <$ dssk; }
            ich <- ich `|` fset1 i;
          }
        }
        r <- Some (k, c');
      }
      return r;
    }
  }

  proc run(b) = {
    var b';
    b_ror <- b;

    RO.init();
    h_map <- empty;

    p_map <- empty;
    i_map <- empty;

    m <- 0;
    n <- 0;

    q <- fset0;
    ich <- fset0;
    rch <- fset0;
    xp <- fset0;
    cr <- fset0;

    r_map <- empty;
    resp_inputs <- fset0;

    pk_map <- empty;
    sk_map <- empty;
    c_map <- empty;
    bad_1 <- false;
    bad_2 <- false;
    bad_3 <- false;
    bad_4 <- false;

    b' <@ A(Oracles).distinguish();
    return b';
  }
}.

(* Intermediate games G05-G35 end here *)






(* Lemmas and proofs start here *)


(* Lemma for Hop0 *)

local lemma Hop0 &m:
  `|  Pr[Exp_b(SignedDH(S), RO, A).run(false) @ &m: res]
    - Pr[Exp_b(SignedDH(S), RO, A).run(true ) @ &m: res] |
  = `|  Pr[Game0_b.run(false) @ &m: res]
      - Pr[Game0_b.run(true ) @ &m: res] |.

proof.
have ^ + -> - -> //:
  forall b, Pr[Exp_b(SignedDH(S), RO, A).run(b) @ &m: res]
          = Pr[Game0_b.run(b) @ &m: res].
move=> b; byequiv (: ={glob A, glob S, arg} ==> ={res})=> //.
proc.
(* The calls are equivalent due to equality on a bunch of variables *)
call (: ={glob Exp_b(SignedDH(S), RO)}); last first.
(* The invariant holds initially and allows us to conclude *)
+ by inline *; auto.
(* The invariant is preserved by all oracles *)
+ by proc; inline *; auto; call (: true); auto.
+ by proc; inline *; auto.
+ by proc; inline *; auto.
+ by proc; inline *; sim; auto.
+ proc; inline *; sp; if; auto.
  sim; auto.
  by call (: true); auto.
+ proc; sp; if; auto; sp; if; auto.
  inline {1} 1.
  by sim; auto.
+ conseq (: _ ==> ={glob RO, res})=> //.
  by sim.
qed.


(** Each hop first introduces a flag-only intermediate game by perfect
    equivalence, then bounds its difference from the next game by bad. **)

(* The existing losslessness assumptions let the two executions continue
   independently once the later game's bad flag is set. *)
(* For all oracles that terminate, the adversary terminates *)
declare axiom A_ll (O <: UAKE_RO_Oracles {-A}):
     islossless O.gen
  => islossless O.corrupt
  => islossless O.expose
  => islossless O.init
  => islossless O.respond
  => islossless O.receive
  => islossless O.h
  => islossless A(O).distinguish.

declare axiom S_keygen_ll: islossless S.keygen.
declare axiom S_sign_ll: islossless S.sign.



(* Lemma for Hop1 *)

local lemma Hop1 (b : bool) &m:
  `|Pr[Game0_b.run(b) @ &m: res] - Pr[Game1_b.run(b) @ &m: res]|
  <= Pr[Game1_b.run(b) @ &m: Game1_b.bad_1].

(* Proof below by GPT-6.1-Sol *)

proof.
have ->: Pr[Game0_b.run(b) @ &m: res] = Pr[Game05_b.run(b) @ &m: res].
+ byequiv (: ={glob A, glob S, b} ==> ={res})=> //; proc.
  call (: ={glob Exp_b, glob S, glob RO}); [2..7:by sim|8:by inline; auto].
  by proc; auto; call (: true); auto=> />.

byequiv: Game1_b.bad_1=> [||/#] //.
proc.

call (: Game1_b.bad_1
      , ={glob Exp_b, glob S, glob RO, Game1_b.bad_1}
      , ={Game1_b.bad_1}).

+ exact: A_ll.

+ by proc; auto; call (: true); auto.

+ move=> &2 bad; proc; auto=> />.
  by call S_keygen_ll; auto=> />; rewrite bad.

+ move=> &1; proc; auto.
  by call S_keygen_ll; auto=> />.

+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.

+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, res})=> //.
  by sim.
+ by move=> &2 bad; proc; auto.
+ by move=> &1; proc; auto.

+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, res})=> //.
  by sim.
+ move=> &2 bad; proc; auto=> /> &0.
  by rewrite dsk_ll /= /#.
+ move=> &1; proc; auto=> /> &0.
  by rewrite dsk_ll /= /#.

+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, res})=> //.
  by sim.
+ move=> &2 bad; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
+ move=> &1; conseq (: true); proc; islossless.
  + by match; islossless.
  + exact: S_sign_ll.

+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, res})=> //.
  by sim.
+ move=> &2 bad; conseq (: true); proc; islossless.
+ move=> &1; conseq (: true); proc; islossless.

+ conseq (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1, res})=> //.
  by sim.
+ by move=> &2 bad; conseq (: true); proc; islossless.
+ by move=> &1; conseq (: true); proc; islossless.

by inline; auto=> /> /#.
qed.


(* Lemma for Hop2 *)

local lemma Hop2 b &m:
  `|Pr[Game1_b.run(b) @ &m: res] - Pr[Game2_b.run(b) @ &m: res]|
  <= Pr[Game2_b.run(b) @ &m: Game2_b.bad_2].

(* Proofs and definitions below by GPT-6.1-Sol *)

proof.
  have ->: Pr[Game1_b.run(b) @ &m: res] = Pr[Game15_b.run(b) @ &m: res].
  + byequiv (: ={glob A, glob S, b} ==> ={res})=> //; proc.
    call (: ={glob Exp_b, glob S, glob RO, Game1_b.bad_1});
      [1..3,6..7: by sim |8: by inline; auto].
    proc; seq 2 2: (={pk,x,c,glob Exp_b,glob S,glob RO,Game1_b.bad_1}).
    + by auto=> />.
    + if{2}; first sp 0 1.
      + by sp 2 2; sim.
      + by sp 2 2; sim.
    + proc; sp; if; [by auto | sp 0 1; by sim | by auto].
  byequiv: Game2_b.bad_2=> [||/#] //.
  proc.
  call (: Game2_b.bad_2,
    ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game2_b.bad_2},
    ={Game2_b.bad_2}).
  + exact A_ll.
  + conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game2_b.bad_2, res})=> //.
    by sim.
  + by move=> &2 bad; conseq (:true); proc; islossless; exact S_keygen_ll.
  + by move=> &1; conseq (:true); proc; islossless; exact S_keygen_ll.
  + conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game2_b.bad_2, res})=> //.
    by sim.
  + by move=> &2 bad; proc; auto.
  + by move=> &1; proc; auto.
  + conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game2_b.bad_2, res})=> //.
    by sim.
  + by move=> &2 bad; proc; auto.
  + by move=> &1; proc; auto.
  + proc; seq 2 2: (={pk,x,c,glob Exp_b, Game2_b.resp_inputs,glob S,glob RO,Game1_b.bad_1,Game2_b.bad_2}).
    + by auto=> />.
    + if.
      + by auto=> />.
      + sp; match{1}; auto.
      + conseq (: ={c,glob Exp_b, Game2_b.resp_inputs,glob S,glob RO,Game1_b.bad_1,Game2_b.bad_2})=> //.
        by sp 2 2; sim.

  + by move=> &2 bad; proc; auto=> />; smt(dsk_ll).
  + by move=> &1; proc; auto=> />; smt(dsk_ll).
  + conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game2_b.bad_2, res})=> //.
    by sim.
  + move=> &2 bad; conseq (:true); proc; islossless.
    + by match; islossless.
    + exact S_sign_ll.
  + move=> &1; conseq (:true); proc; islossless.
    + by match; islossless.
    + exact S_sign_ll.
  + conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game2_b.bad_2, res})=> //.
    by sim.
  + by move=> &2 bad; conseq (:true); proc; islossless.
  + by move=> &1; conseq (:true); proc; islossless.
  + conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game2_b.bad_2, res})=> //.
    by sim.
  + by move=> &2 bad; conseq (:true); proc; islossless.
  + by move=> &1; conseq (:true); proc; islossless.
  by inline; auto=> /> /#.
qed.

(* The abstract client-collision bound below is an explicit
   probability hypothesis. *)

op p_2 : real.
local lemma Bad2 b &m:
  Pr[Game2_b.run(b) @ &m: Game2_b.bad_2] <= p_2 =>
  `|Pr[Game1_b.run(b) @ &m: res] - Pr[Game2_b.run(b) @ &m: res]| <= p_2.
proof.
  by move=> hp; exact (ler_trans _ _ _ (Hop2 b &m) hp).
qed.


(* Lemma for Hop3 *)

local lemma Hop3 b &m:
  `|Pr[Game2_b.run(b) @ &m: res] - Pr[Game3_b.run(b) @ &m: res]|
  <= Pr[Game3_b.run(b) @ &m: Game3_b.bad_3].

(* Proof below by GPT-6.1-Sol *)

proof.
have ->: Pr[Game2_b.run(b) @ &m: res] = Pr[Game25_b.run(b) @ &m: res].
+ byequiv (: ={glob A, glob S, b} ==> ={res})=> //; proc.
  call (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1}); [1..5,7:by sim|8:by inline; auto].
  proc; sp; if; auto; sp; if; auto; sp 1 1.
    seq 1 1: (={i, c, ch, st_i, h, sig, b, ko,
      glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1}).
    + by auto.
    seq 1 1: (={i, c, ch, ko,
      glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1}).
    + by sim.
    case (ch{1}).
    + if; first by auto=> /> /#.
      + sp 0 1; if; auto=> /> /#.
      + by auto=> /> /#.
    + rcondf{1} 1; first by auto=> /> /#.
      if{2}.
      + sp 0 1; rcondf{2} 1; first by auto=> /> /#.
        by auto=> />; smt(sub1set subset_fsetU_id fsetUC).
      + by auto=> /> /#.

byequiv: Game3_b.bad_3=> [||/#] //.
proc.
call (: Game3_b.bad_3,
        ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3},
        ={Game3_b.bad_3}).

+ exact: A_ll.
+ conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3, res})=> //.
  by proc; inline *; sim; auto=> /> /#.
+ move=> &2 bad; proc; inline *; auto.
  by call S_keygen_ll; auto=> />.
+ move=> &1; proc; inline *; auto.
  by call S_keygen_ll; auto=> />.
+ conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3, res})=> //.
  by proc; inline *; sim; auto=> /> /#.
+ by move=> &2 bad; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
+ conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3, res})=> //.
  by proc; inline *; sim; auto=> /> /#.
+ by move=> &2 bad; proc; inline *; auto.
+ by move=> &1; proc; inline *; auto.
+ conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3, res})=> //.
  by proc; inline *; sim; auto=> /> /#.
+ move=> &2 bad; proc; inline *; auto=> /> &0.
  by rewrite dsk_ll /= /#.
+ move=> &1; proc; inline *; auto=> /> &0.
  by rewrite dsk_ll /= /#.
+ conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3, res})=> //.
  proc; inline *; sp; if; auto.
  sim; auto.
+ move=> &2 bad; conseq (: true); proc; inline *; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
+ move=> &1; conseq (: true); proc; inline *; islossless.
  + by match; islossless.
  + exact: S_sign_ll.
+ proc; sp; if.
  + by auto=> /> /#.
  + sp; if.
    + by auto=> /> /#.
    + sp 1 1.
      seq 1 1 : (={i, c, ch, st_i, h, sig, b, ko,
                    glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3}).
      + by auto.
      seq 1 1 : (={i, c, ch, ko,
                    glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3}).
      + by sim.
      if; first by auto=> /> /#.
      + sp 1 1; if{1}; auto.
      + by auto=> /> /#.
    + by auto=> /> /#.
  + by auto=> /> /#.
+ move=> &2 bad.
  conseq (: true ==> true)
         (: Game3_b.bad_3 = Game3_b.bad_3{2} ==> Game3_b.bad_3 = Game3_b.bad_3{2})=> //.
  + proc; inline *; sp; if; auto.
    sp; if; auto; sp 1.
    seq 1 : (Game3_b.bad_3 = Game3_b.bad_3{2}).
    + by auto.
    + seq 1 : (Game3_b.bad_3 = Game3_b.bad_3{2}).
      + by if; auto.
      + if; auto.
        sp; if; auto=> />; rewrite bad //.
  + proc; inline *; islossless.
+ move=> &1.
  conseq (: true ==> true)
         (: Game3_b.bad_3 /\ Game3_b.bad_3{1} = Game3_b.bad_3
            ==> Game3_b.bad_3 /\ Game3_b.bad_3{1} = Game3_b.bad_3)=> //.
  + proc; inline *; sp; if; auto.
    sp; if; auto; sp 1.
    seq 1 : (Game3_b.bad_3 /\ Game3_b.bad_3{1} = Game3_b.bad_3).
    + by auto.
    + seq 1 : (Game3_b.bad_3 /\ Game3_b.bad_3{1} = Game3_b.bad_3).
      + by if; auto.
      + by auto=> /> /#.
  + proc; inline *; islossless.
+ conseq (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3, res})=> //.
  by proc; inline *; sim; auto=> /> /#.
+ by move=> &2 bad; conseq (: true); proc; inline *; islossless.
+ by move=> &1; conseq (: true); proc; inline *; islossless.
by inline; auto=> /> /#.
qed.


(** Signature reduction for Hop3:
    bad_3 yields a native SUF-CMA forgery.
    A single relational proof handles both challenge bits; the two probability
    bounds below specialize it to false and true. **)

(* Proofs and definitions below by GPT-6.1-Sol *)

local module SigR = SUFCMA(S,B1(S,A)).
local module SigSim = B1(S,A,SigR.Oracles).

op sig_shape n m ns
 (cm:(int,client_state) fmap) (pm:(int,int) fmap) (im:(int,pdh) fmap)
 (pkm:(int,pkey) fmap) (skm:(int,skey) fmap) (idx:(int,int) fmap)
 (npk:(int,pkey) fmap) (nsk:(int,skey) fmap) (cr ncr:int fset)
 (uq:(int*(pdh*pdh)*sig) fset) (hist:pdh fset)
 (rm:(int option*int,(pdh*sig) fset) fmap) =
 0<=n /\ 0<=m /\ 0<=ns /\
 (forall i, cm.[i]<>None <=> 0<i<=n) /\
 (forall j, pkm.[j]<>None <=> 0<j<=m) /\
 (forall j, idx.[j]<>None <=> 0<j<=m) /\
 (forall j a, idx.[j]=Some a => 0<a<=ns /\ npk.[a]=pkm.[j] /\ nsk.[a]=skm.[j]) /\
 (forall j j' a, idx.[j]=Some a => idx.[j']=Some a => j=j') /\
 (forall i j, pm.[i]=Some j => 0<i<=n /\ 0<j<=m /\
   pkm.[j]=Some (oget cm.[i]).`pk /\ im.[i]=Some (oget cm.[i]).`epk) /\
 (forall i i' st st', cm.[i]=Some st => cm.[i']=Some st' => st.`epk=st'.`epk => i=i') /\
 (forall j, j \in cr => 0<j<=m) /\
 (forall a, a \in ncr => 0<a<=ns) /\
 (forall j, 0<j<=m => (oget idx.[j] \in ncr <=> j \in cr)) /\
 (forall a x y ss, (a,(x,y),ss) \in uq => x \in hist) /\
 (forall i st j y ss, cm.[i]=Some st => pm.[i]=Some j =>
   (oget idx.[j],(st.`epk,y),ss) \in uq =>
   (y,ss) \in odflt fset0 rm.[Some j,i]).

local abbrev sig_inv (sl sr:glob S) (el:glob Exp_b) (br:glob B1)
 (su:glob SUFCMA) (hist:pdh fset) =
 let (bl,cl,crl,il,ichl,ml,nl,pl,pkl,ql,rl,rchl,skl,xpl)=el in
 let (brr,bd,cc,crr,ff,ii,ichr,mr,ms,nr,pp,pkr,qr,rr,rchr,tt,idx,xpr,hcache)=br in
 let (ncr,ns,npk,uq,nsk)=su in
 sl=sr /\ ff=None /\ bl=brr /\ nl=nr /\ ml=mr /\ ms=ns /\
 cl=cc /\ crl=crr /\ il=ii /\ ichl=ichr /\ pl=pp /\ pkl=pkr /\
 ql=qr /\ rl=rr /\ rchl=rchr /\ xpl=xpr /\ hist=tt /\
 sig_shape nl ml ns cl pl il pkl skl idx npk nsk crr ncr uq hist rl.

op sig_success (f:(int*(pdh*pdh)*sig) option) ns
 (pkm:(int,pkey) fmap) (cr:int fset) (q:(int*(pdh*pdh)*sig) fset) =
 f<>None /\ let (j,msg,ss)=oget f in
 0<j<=ns /\ j \notin cr /\ (j,msg,ss) \notin q /\ verify(oget pkm.[j],msg,ss).

local lemma sig_capture n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm i st j y ss:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 cm.[i]=Some st => pm.[i]=Some j => j \notin cr =>
 (y,ss) \notin odflt fset0 rm.[Some j,i] =>
 verify(st.`pk,(st.`epk,y),ss) =>
 sig_success (Some (oget idx.[j],(st.`epk,y),ss)) ns npk ncr uq.
proof.
 move=> hs hc hp hn hr hv.
 have hj:0<j<=m by rewrite /sig_shape in hs; smt().
 have hi:idx.[j]=Some (oget idx.[j]) by rewrite /sig_shape in hs; smt(get_some).
 have hk:npk.[oget idx.[j]]=Some st.`pk by rewrite /sig_shape in hs; smt(oget_some).
 have hf:(oget idx.[j],(st.`epk,y),ss) \notin uq by rewrite /sig_shape in hs; smt().
 rewrite /sig_success /= hk oget_some; rewrite /sig_shape in hs; smt().
qed.

local lemma sig_shape_gen n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm pk sk:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 sig_shape n (m+1) (ns+1) cm pm im pkm.[m+1<-pk] skm.[m+1<-sk]
  idx.[m+1<-ns+1] npk.[ns+1<-pk] nsk.[ns+1<-sk] cr ncr uq hist rm.
proof.
 rewrite /sig_shape; progress; smt(get_setE).
qed.

local lemma sig_shape_reject n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm pk sk:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 sig_shape n m (ns+1) cm pm im pkm skm idx npk.[ns+1<-pk] nsk.[ns+1<-sk] cr ncr uq hist rm.
proof.
 rewrite /sig_shape; smt(get_setE).
qed.

local lemma sig_shape_corrupt n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm j:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 0<j<=m =>
 sig_shape n m ns cm pm im pkm skm idx npk nsk
  (cr `|` fset1 j) (ncr `|` fset1 (oget idx.[j])) uq hist rm.
proof.
 rewrite /sig_shape; smt(in_fsetU in_fset1 get_some domE).
qed.

local lemma sig_shape_find n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm j c:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 find (fun i _=>pm.[i]=Some j /\ im.[i]=Some c) cm =
 find (fun i jj=>jj=j /\ im.[i]=Some c) pm.
proof.
 move=> hs; case (findP (fun i jj=>jj=j /\ im.[i]=Some c) pm).
 + move=> hn hnone; rewrite hn; apply find_eq_none.
   move=> a ha; rewrite /sig_shape in hs; smt(domE oget_some).
 + move=> a jj hf hpm [hj him]; rewrite hf.
   have hpos:0<a<=n by rewrite /sig_shape in hs; smt().
   have hcm:cm.[a]=Some (oget cm.[a]) by rewrite /sig_shape in hs; smt(get_some domE).
   apply uniq_find_eq_some.
   + move=> b st hb [hpm_b him_b].
     have hst_b:st.`epk=c by rewrite /sig_shape in hs; smt(oget_some).
     have hst_a:(oget cm.[a]).`epk=c by rewrite /sig_shape in hs; smt(oget_some).
     rewrite /sig_shape in hs; smt().
   + by rewrite domE hcm.
   + by smt().
qed.

local lemma sig_shape_init_none n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm pk c x:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 !has (fun _ st=>st.`epk=c) cm => c \notin hist =>
 sig_shape (n+1) m ns cm.[n+1<-{|pk=pk;epk=c;esk=x;|}]
  pm im pkm skm idx npk nsk cr ncr uq hist rm.
proof.
 rewrite /sig_shape hasP; progress; smt(get_setE).
qed.

local lemma sig_shape_init_some n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm pk c x j:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 !has (fun _ st=>st.`epk=c) cm => c \notin hist => pkm.[j]=Some pk =>
 sig_shape (n+1) m ns cm.[n+1<-{|pk=pk;epk=c;esk=x;|}]
  pm.[n+1<-j] im.[n+1<-c] pkm skm idx npk nsk cr ncr uq hist rm.
proof.
 rewrite /sig_shape hasP; progress; smt(get_setE oget_some).
qed.

op sig_reply_map (rm:(int option*int,(pdh*sig) fset) fmap) (io:int option) j reply =
 if io=None then rm else
 rm.[Some j,oget io<-odflt fset0 rm.[Some j,oget io] `|` fset1 reply].

local lemma sig_reply_map_mem rm io j reply key oldreply:
 oldreply \in odflt fset0 rm.[key] =>
 oldreply \in odflt fset0 (sig_reply_map rm io j reply).[key].
proof.
 rewrite /sig_reply_map; case io=> [|i] /=; first by trivial.
 rewrite get_setE; smt(in_fsetU).
qed.

local lemma sig_partner_find n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm i st j c:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm =>
 cm.[i]=Some st => pm.[i]=Some j => st.`epk=c =>
 find (fun a jj=>jj=j /\ im.[a]=Some c) pm=Some i.
proof.
 move=> hs hc hp he; apply uniq_find_eq_some.
 + move=> a jj ha [hj hi].
   have hac:cm.[a]=Some (oget cm.[a]) by rewrite /sig_shape in hs; smt(get_some domE).
   rewrite /sig_shape in hs; smt(oget_some).
 + by rewrite domE hp.
 + rewrite /sig_shape in hs; smt(oget_some).
qed.

local lemma sig_shape_response n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm j c h ss:
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm => 0<j<=m =>
 sig_shape n m ns cm pm im pkm skm idx npk nsk cr ncr
  (uq `|` fset1 (oget idx.[j],(c,h),ss)) (hist `|` fset1 c)
  (sig_reply_map rm (find (fun a jj=>jj=j /\ im.[a]=Some c) pm) j (h,ss)).
proof.
 move=> hs hj.
 have hreply: forall i st jj y sig, cm.[i]=Some st => pm.[i]=Some jj =>
  (oget idx.[jj],(st.`epk,y),sig) \in (uq `|` fset1 (oget idx.[j],(c,h),ss)) =>
  (y,sig) \in odflt fset0
   (sig_reply_map rm (find (fun a jj=>jj=j /\ im.[a]=Some c) pm) j (h,ss)).[Some jj,i].
 + move=> i st jj y sig hc hp; rewrite in_fsetU in_fset1; move=> [hlog|heq].
   + have hm:(y,sig) \in odflt fset0 rm.[Some jj,i] by rewrite /sig_shape in hs; smt().
     exact (sig_reply_map_mem rm _ j (h,ss) (Some jj,i) (y,sig) hm).
   + have hjj:0<jj<=m by rewrite /sig_shape in hs; smt().
     have hi:idx.[j]=Some (oget idx.[j]) by rewrite /sig_shape in hs; smt(get_some).
     have hii:idx.[jj]=Some (oget idx.[jj]) by rewrite /sig_shape in hs; smt(get_some).
     have he:jj=j by rewrite /sig_shape in hs; smt().
     have hep:st.`epk=c by smt().
     have hf:=sig_partner_find n m ns cm pm im pkm skm idx npk nsk cr ncr uq hist rm i st j c hs hc _ hep.
     - by rewrite -he.
     - rewrite he /sig_reply_map hf /=.
       smt(get_setE in_fsetU in_fset1).
 rewrite /sig_shape; smt(in_fsetU in_fset1).
qed.

local lemma sig_gen_state:
 equiv[Game3_b.Oracles.gen ~ SigSim.Oracles.gen:
 !Game3_b.bad_3{1} /\ ={glob RO} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> !Game3_b.bad_3{1} /\ ={glob RO,res} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}].
proof.
 proc; rcondt{2} 2; first by auto=> />; rewrite /sig_inv /=; smt().
 inline{2} SigR.Oracles.gen.
 auto; call (:true); auto=> />.
 move=> &1 &2 hbad hn hm hns hcm hpk hidx hkeys hinj hp hu hcr hncr hc hq hlog [pk sk].
 have hs: sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} by rewrite /sig_shape; smt().
 have hg:=sig_shape_gen B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} pk sk hs.
 have hr:=sig_shape_reject B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} pk sk hs.
 rewrite /sig_shape in hg; rewrite /sig_shape in hr; smt().
qed.

local lemma sig_corrupt_state:
 equiv[Game3_b.Oracles.corrupt ~ SigSim.Oracles.corrupt:
 !Game3_b.bad_3{1} /\ ={arg,glob RO} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> !Game3_b.bad_3{1} /\ ={glob RO,res} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}].
proof.
 proc; rcondt{2} 2; first by auto=> />; rewrite /sig_inv /=; smt().
 inline{2} SigR.Oracles.corrupt.
 auto.
 move=> &1 &2 hs.
 smt(sig_shape_corrupt).
qed.

local lemma sig_expose_state:
 equiv[Game3_b.Oracles.expose ~ SigSim.Oracles.expose:
 !Game3_b.bad_3{1} /\ ={arg,glob RO} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> !Game3_b.bad_3{1} /\ ={glob RO,res} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}].
proof.
 proc; rcondt{2} 2; first by auto=> />; rewrite /sig_inv /=; smt().
 auto=> />; rewrite /sig_inv /=; smt().
qed.

local lemma sig_h_state:
 equiv[Game3_b.Oracles.h ~ SigSim.Oracles.h:
 !Game3_b.bad_3{1} /\ ={arg,glob RO} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> !Game3_b.bad_3{1} /\ ={glob RO,res} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}].
proof.
 proc *; inline{2} SigSim.Oracles.h; sp.
 rcondt{2} 1; first by auto=> />; smt().
 wp; call (_: ={glob RO}); auto=> />.
qed.

local lemma sig_init_state:
 equiv[Game3_b.Oracles.init ~ SigSim.Oracles.init:
 !Game3_b.bad_3{1} /\ ={arg,glob RO} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> !Game3_b.bad_3{1} /\ ={glob RO,res} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}].
proof.
 proc; rcondt{2} 2; first by auto=> />; smt().
 auto=> />.
 move=> &1 &2 hbad hn hm hns hcm hpk hidx hkeys hinj hp hu hcr hncr hc hq hlog x hx.
 have hs:sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} by rewrite /sig_shape; smt().
 case (has (fun _ st=>st.`epk=g^x) B1.c_map{2} \/ g^x \in B1.resp_inputs{2})=> hcol.
 + by smt().
 + have hf:!has (fun _ st=>st.`epk=g^x) B1.c_map{2} by smt().
   have ht:g^x \notin B1.resp_inputs{2} by smt().
   case (findP (fun _ pkj=>pkj=pk{2}) B1.pk_map{2}).
   + move=> hfind hnone.
     have hi:=sig_shape_init_none B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} pk{2} (g^x) x hs hf ht.
     rewrite hfind /=; smt().
   + move=> j pkj hfind hj heq.
     have hjpk:B1.pk_map{2}.[j]=Some pk{2} by smt().
     have hi:=sig_shape_init_some B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} pk{2} (g^x) x j hs hf ht hjpk.
     rewrite hfind /=; smt().
qed.

local lemma sig_respond_state:
 equiv[Game3_b.Oracles.respond ~ SigSim.Oracles.respond:
 !Game3_b.bad_3{1} /\ ={arg,glob RO} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> !Game3_b.bad_3{1} /\ ={glob RO,res} /\
 sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}].
proof.
 proc; rcondt{2} 2; first by auto=> />; smt().
 sp 1 1; if.
 + by auto=> />; smt().
 + inline{2} SigR.Oracles.sign.
   rcondt{2} 7.
   + auto=> />; smt(get_some).
   + swap{1} 1 9; swap{2} 1 15; swap{2} 8 8.
     seq 4 7:(!Game3_b.bad_3{1} /\ ={glob RO,j,c,ch,y,h} /\
      sig{1}=sig0{2} /\ sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1} /\ 0<j{1}<=Exp_b.m{1} /\
      j0{2}=oget B1.sig_idx{2}.[j{2}] /\ m{2}=(c{2},h{2})).
     + auto; call (:true); auto=> />; smt(get_some).
     + seq 2 4:(!Game3_b.bad_3{1} /\ ={glob RO,j,c,ch,y,h,c',k} /\
       c'{1}=(h{1},sig{1}) /\ sig{1}=sig0{2} /\
       sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1} /\ 0<j{1}<=Exp_b.m{1} /\
       j0{2}=oget B1.sig_idx{2}.[j{2}] /\ m{2}=(c{2},h{2})).
       + auto; call (_: ={glob RO}); auto=> />; smt().
       + seq 1 1:(!Game3_b.bad_3{1} /\ ={glob RO,j,c,ch,y,h,c',k,io} /\
         c'{1}=(h{1},sig{1}) /\ sig{1}=sig0{2} /\
         sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1} /\ 0<j{1}<=Exp_b.m{1} /\
         j0{2}=oget B1.sig_idx{2}.[j{2}] /\ m{2}=(c{2},h{2}) /\
         io{2}=find (fun i jj=>jj=j{2} /\ B1.i_map{2}.[i]=Some c{2}) B1.p_map{2}).
         + auto; move=> &1 &2 hs.
           have ht:sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} by smt().
           have hf:=sig_shape_find B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} j{2} c{2} ht.
           have hc:Exp_b.c_map{1}=B1.c_map{2} by smt().
           have hp:Exp_b.p_map{1}=B1.p_map{2} by smt().
           have hi:Exp_b.i_map{1}=B1.i_map{2} by smt().
           have hj:j{1}=j{2} by smt().
           have he:c{1}=c{2} by smt().
           rewrite hc hp hi hj he hf /=; smt().
         + match.
           + by auto=> />.
           + by auto=> />.
           + auto; move=> &1 &2 hs.
             have ht:sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} by smt().
             have hj:0<j{2}<=B1.m{2} by smt().
             have he:=sig_shape_response B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} j{2} c{2} h{2} sig0{2} ht hj.
             rewrite /sig_reply_map in he; smt().
           + move=> i i0; exists* B1.r_map{2}; elim*=> rm0.
             sp 1 1; if.
             + by auto=> />; smt().
             + if.
               + by auto=> />; smt().
               + auto; move=> &1 &2 hs.
               have ht:sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} rm0 by smt().
               have hj:0<j{2}<=B1.m{2} by smt().
               have hf:find (fun a jj=>jj=j{2} /\ B1.i_map{2}.[a]=Some c{2}) B1.p_map{2}=Some i0 by smt().
               have he:=sig_shape_response B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} rm0 j{2} c{2} h{2} sig0{2} ht hj.
               rewrite /sig_reply_map hf /= in he; smt().
               + auto; move=> &1 &2 hs.
               have ht:sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} rm0 by smt().
               have hj:0<j{2}<=B1.m{2} by smt().
               have hf:find (fun a jj=>jj=j{2} /\ B1.i_map{2}.[a]=Some c{2}) B1.p_map{2}=Some i0 by smt().
               have he:=sig_shape_response B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} rm0 j{2} c{2} h{2} sig0{2} ht hj.
               rewrite /sig_reply_map hf /= in he; smt().
             + auto; move=> &1 &2 hs.
               have ht:sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} rm0 by smt().
               have hj:0<j{2}<=B1.m{2} by smt().
               have hf:find (fun a jj=>jj=j{2} /\ B1.i_map{2}.[a]=Some c{2}) B1.p_map{2}=Some i0 by smt().
               have he:=sig_shape_response B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} rm0 j{2} c{2} h{2} sig0{2} ht hj.
               rewrite /sig_reply_map hf /= in he; smt().
 + by auto=> />.
qed.

local lemma sig_receive_state:
 equiv[Game3_b.Oracles.receive ~ SigSim.Oracles.receive:
 !Game3_b.bad_3{1} /\ ={arg,glob RO} /\ sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> (!Game3_b.bad_3{1} => ={glob RO,res} /\ sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}) /\
 (Game3_b.bad_3{1} => sig_success B1.forgery{2} SUFCMA.n{2} SUFCMA.pk_map{2} SUFCMA.cr{2} SUFCMA.q{2})].
proof.
 proc; rcondt{2} 2; first by auto=> />; smt().
 sp 1 1; if.
 + by auto=> />; smt().
 + sp 2 2; if.
   + by auto=> />; smt().
   + seq 3 3:(!Game3_b.bad_3{1} /\ ={glob RO,i,c,ch,st_i,h,sig,b,ko} /\
     sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1} /\ Exp_b.c_map{1}.[i{1}]=Some st_i{1} /\
     c{1}=(h{1},sig{1}) /\
     c{1} \notin odflt fset0 Exp_b.r_map{1}.[Exp_b.p_map{1}.[i{1}],i{1}] /\
     (ko{1}<>None => verify(st_i{1}.`pk,(st_i{1}.`epk,h{1}),sig{1}))).
     + sp 2 2; if.
       + by auto=> />; smt().
       + wp; call (_: ={glob RO}); auto=> />; smt(get_some).
       + by auto=> />; smt(get_some).
     + if.
       + by auto=> />; smt().
       + rcondt{2} 1; first by auto=> />; smt().
         sp 0 1; if{2}; [wp; rnd{2}|]; auto; move=> &1 &2 hs;
         (have ht:sig_shape B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} by smt());
         (have hc:B1.c_map{2}.[i{2}]=Some st_i{2} by smt());
         (have hp:B1.p_map{2}.[i{2}]=Some (oget B1.p_map{2}.[i{2}]) by smt(get_some));
         (have hn:oget B1.p_map{2}.[i{2}] \notin B1.cr{2} by smt());
         (have hr:(h{2},sig{2}) \notin odflt fset0 B1.r_map{2}.[Some (oget B1.p_map{2}.[i{2}]),i{2}] by smt());
         (have hv:verify(st_i{2}.`pk,(st_i{2}.`epk,h{2}),sig{2}) by smt());
         (have he:=sig_capture B1.n{2} B1.m{2} SUFCMA.n{2} B1.c_map{2} B1.p_map{2} B1.i_map{2} B1.pk_map{2} Exp_b.sk_map{1} B1.sig_idx{2} SUFCMA.pk_map{2} SUFCMA.sk_map{2} B1.cr{2} SUFCMA.cr{2} SUFCMA.q{2} B1.resp_inputs{2} B1.r_map{2} i{2} st_i{2} (oget B1.p_map{2}.[i{2}]) h{2} sig{2} ht hc hp hn hr hv);
         smt(dssk_ll).
       + by auto=> />; smt().
   + by auto=> />; smt().
 + by auto=> />; smt().
qed.

local lemma sig_gen_ll: islossless SigSim.Oracles.gen.
proof.
 proc; inline *; islossless; exact S_keygen_ll.
qed.

local lemma sig_gen_frozen:
 hoare[SigSim.Oracles.gen: sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q ==> sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q].
proof.
 proc; rcondf 2; first by auto=> />; rewrite /sig_success; smt().
 auto.
qed.

local lemma sig_corrupt_ll: islossless SigSim.Oracles.corrupt.
proof.
 proc; inline *; islossless.
qed.

local lemma sig_corrupt_frozen:
 hoare[SigSim.Oracles.corrupt: sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q ==> sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q].
proof.
 proc; rcondf 2; first by auto=> />; rewrite /sig_success; smt().
 auto.
qed.

local lemma sig_expose_ll: islossless SigSim.Oracles.expose.
proof.
 proc; inline *; islossless.
qed.

local lemma sig_expose_frozen:
 hoare[SigSim.Oracles.expose: sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q ==> sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q].
proof.
 proc; rcondf 2; first by auto=> />; rewrite /sig_success; smt().
 auto.
qed.

local lemma sig_init_ll: islossless SigSim.Oracles.init.
proof.
 proc; inline *; islossless; do ?(match; islossless).
qed.

local lemma sig_init_frozen:
 hoare[SigSim.Oracles.init: sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q ==> sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q].
proof.
 proc; rcondf 2; first by auto=> />; rewrite /sig_success; smt().
 auto.
qed.

local lemma sig_respond_ll: islossless SigSim.Oracles.respond.
proof.
 proc; inline *; islossless; try exact S_sign_ll; do ?(match; islossless).
qed.

local lemma sig_respond_frozen:
 hoare[SigSim.Oracles.respond: sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q ==> sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q].
proof.
 proc; rcondf 2; first by auto=> />; rewrite /sig_success; smt().
 auto.
qed.

local lemma sig_receive_ll: islossless SigSim.Oracles.receive.
proof.
 proc; inline *; islossless.
qed.

local lemma sig_receive_frozen:
 hoare[SigSim.Oracles.receive: sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q ==> sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q].
proof.
 proc; rcondf 2; first by auto=> />; rewrite /sig_success; smt().
 auto.
qed.

local lemma sig_h_ll: islossless SigSim.Oracles.h.
proof.
 proc; inline *; islossless.
qed.

local lemma sig_h_frozen:
 hoare[SigSim.Oracles.h: sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q ==> sig_success B1.forgery SUFCMA.n SUFCMA.pk_map SUFCMA.cr SUFCMA.q].
proof.
 proc; rcondf 2; first by auto=> />; rewrite /sig_success; smt().
 auto.
qed.

local lemma sig_game2_receive_ll: islossless Game3_b.Oracles.receive.
proof. proc; inline *; islossless. qed.

local lemma sig_game2_receive_bad:
 hoare[Game3_b.Oracles.receive: Game3_b.bad_3 ==> Game3_b.bad_3].
proof.
 proc; sp; if; last by auto.
 sp 2; if; last by auto.
 sp 2; seq 1:Game3_b.bad_3.
 + if; last by auto.
   by wp; call (:true); auto.
 + by auto=> />; smt().
qed.

local lemma sig_adversary_coupling:
 equiv[A(Game3_b.Oracles).distinguish ~ A(SigSim.Oracles).distinguish:
 ={glob A,glob RO} /\ !Game3_b.bad_3{1} /\ sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1}
 ==> Game3_b.bad_3{1} => sig_success B1.forgery{2} SUFCMA.n{2} SUFCMA.pk_map{2} SUFCMA.cr{2} SUFCMA.q{2}].
proof.
 proc *; call (_: B1.forgery<>None,
  !Game3_b.bad_3{1} /\ ={glob RO} /\ sig_inv (glob S){1} (glob S){2} (glob Exp_b){1} (glob B1){2} (glob SUFCMA){2} Game2_b.resp_inputs{1},
  Game3_b.bad_3{1} /\ sig_success B1.forgery{2} SUFCMA.n{2} SUFCMA.pk_map{2} SUFCMA.cr{2} SUFCMA.q{2}).
 + exact A_ll.
 + by conseq sig_gen_state=> //; rewrite /sig_success; smt().
 + move=> &2 hbad; proc; auto; call S_keygen_ll; auto=> />; smt().
 + by move=> &1; conseq sig_gen_ll sig_gen_frozen=> //; smt().
 + by conseq sig_corrupt_state=> //; rewrite /sig_success; smt().
 + by move=> &2 hbad; proc; auto=> />; smt().
 + by move=> &1; conseq sig_corrupt_ll sig_corrupt_frozen=> //; smt().
 + by conseq sig_expose_state=> //; rewrite /sig_success; smt().
 + by move=> &2 hbad; proc; auto=> />; smt().
 + by move=> &1; conseq sig_expose_ll sig_expose_frozen=> //; smt().
 + by conseq sig_init_state=> //; rewrite /sig_success; smt().
 + move=> &2 hbad; proc; auto=> />; smt(dsk_ll).
 + by move=> &1; conseq sig_init_ll sig_init_frozen=> //; smt().
 + by conseq sig_respond_state=> //; smt().
 + move=> &2 hbad; conseq (:true)=> //; proc.
   inline *; islossless; try exact S_sign_ll; do ?(match; islossless).
 + by move=> &1; conseq sig_respond_ll sig_respond_frozen=> //; smt().
 + by conseq sig_receive_state=> //; smt().
 + by move=> &2 hbad; conseq sig_game2_receive_ll sig_game2_receive_bad=> //; smt().
 + by move=> &1; conseq sig_receive_ll sig_receive_frozen=> //; smt().
 + by conseq sig_h_state=> //; smt().
 + move=> &2 hbad; proc; auto=> />; smt(dssk_ll).
 + by move=> &1; conseq sig_h_ll sig_h_frozen=> //; smt().
 + by auto=> />; rewrite /sig_success; smt().
qed.




(* Local equivalence for signature reduction (Hop3) *)

local equiv Reduction1_equiv:
  Game3_b.run ~ SUFCMA(S, B1(S, A)).run:
       ={glob A, glob S, glob RO}
    /\ b{1} = B1.b_ror{2}
    ==> Game3_b.bad_3{1} => res{2}.
proof.
 proc; inline{2} SigSim.forge.
 auto; call sig_adversary_coupling; inline RO.init.
 auto=> />; rewrite /sig_success; smt(FMap.emptyE in_fset0).
qed.


(* Lemma for signature reduction with bit 0 (Hop3) *)

local lemma Reduction1_0 &m:
  Pr[Game3_b.run(false) @ &m: Game3_b.bad_3]
  <= Pr[SUFCMA(S, B1_0(S, A)).run() @ &m: res].

proof.
byequiv (: ={glob A, glob S, glob RO} /\ !b{1} ==> Game3_b.bad_3{1} => res{2})=> //.
proc *.
transitivity {2}
  { B1.b_ror <- false;
    r <@ SUFCMA(S, B1(S, A)).run(); }
  (={glob A, glob S, glob RO} /\ !b{1} ==> Game3_b.bad_3{1} => r{2})
  (={glob A, glob S, glob RO} ==> ={r})=> [/#|/>||].
+ by call Reduction1_equiv; auto=> />.
+ inline *; swap {2} 7 -6.
  sim; wp=> />.
  by sim: (={B1.forgery, b, SUFCMA.q, SUFCMA.cr, SUFCMA.pk_map, SUFCMA.n, glob S})=> />.
qed.


(* Lemma for signature reduction with bit 1 (Hop3) *)

local lemma Reduction1_1 &m:
  Pr[Game3_b.run(true) @ &m: Game3_b.bad_3]
  <= Pr[SUFCMA(S, B1_1(S, A)).run() @ &m: res].

proof.
byequiv (: ={glob A, glob S, glob RO} /\ b{1} ==> Game3_b.bad_3{1} => res{2})=> //.
proc *.
transitivity {2}
  { B1.b_ror <- true;
    r <@ SUFCMA(S, B1(S, A)).run(); }
  (={glob A, glob S, glob RO} /\ b{1} ==> Game3_b.bad_3{1} => r{2})
  (={glob A, glob S, glob RO} ==> ={r})=> [/#|/>||].
+ by call Reduction1_equiv; auto=> />.
+ inline *; swap {2} 7 -6.
  sim; wp=> />.
  by sim: (={B1.forgery, b, SUFCMA.q, SUFCMA.cr, SUFCMA.pk_map, SUFCMA.n, glob S})=> />.
qed.


(* Hop4 *)
(* Definitions and proofs below by GPT-6.1-Sol *)

op hop4_clients (cm : (int, client_state) fmap) =
  forall i st, cm.[i] = Some st => st.`esk \in dsk /\ st.`epk = g ^ st.`esk.

op hop4_valid (cm : (int, client_state) fmap) (z x y : pdh) =
  has (fun _ st=> st.`epk = x /\ z = y ^ st.`esk) cm.

op hop4_key (cm : (int, client_state) fmap) (zxy : pdh * pdh * pdh) =
  (if hop4_valid cm zxy.`1 zxy.`2 zxy.`3 then None else Some zxy.`1, zxy.`2, zxy.`3).

local lemma hop4_clients_set cm i st:
  hop4_clients cm => st.`esk \in dsk => st.`epk = g ^ st.`esk =>
  hop4_clients cm.[i <- st].
proof. by rewrite /hop4_clients; smt(get_setE). qed.

local lemma hop4_same_share cm i st j st' y:
  hop4_clients cm => cm.[i] = Some st => cm.[j] = Some st' =>
  st.`epk = st'.`epk => y ^ st.`esk = y ^ st'.`esk.
proof. by rewrite /hop4_clients; smt(public_key_injective). qed.

local lemma hop4_find_none (cm : (int, client_state) fmap) x:
  find (fun _ st=> st.`epk = x) cm = None =>
  !has (fun _ st=> st.`epk = x) cm.
proof.
  by case (findP (fun _ (st:client_state)=> st.`epk = x) cm)=> />; smt(hasP domE oget_some).
qed.

local lemma hop4_valid_find cm z x y i:
  hop4_clients cm => find (fun _ st=> st.`epk = x) cm = Some i =>
  (hop4_valid cm z x y <=> z = y ^ (oget cm.[i]).`esk).
proof.
  move=> hc hf.
  have [st [hs he]] := find_some _ _ _ hf.
  rewrite /hop4_valid hasP hs oget_some /=.
  split.
  + move=> [j st' [hs' [he' hz]]].
    by have := hop4_same_share cm i st j st' y hc hs hs'; smt().
  + by move=> hz; exists i st; smt().
qed.

local lemma hop4_valid_none cm z x y:
  find (fun _ st=> st.`epk = x) cm = None => !hop4_valid cm z x y.
proof. by move=> /hop4_find_none; rewrite /hop4_valid !hasP; smt(). qed.

local lemma hop4_key_none cm z x y:
  find (fun _ st=> st.`epk = x) cm = None =>
  hop4_key cm (z,x,y) = (Some z,x,y).
proof. by move=> hf; rewrite /hop4_key /= (hop4_valid_none cm z x y hf). qed.

local lemma hop4_key_find cm z x y i:
  hop4_clients cm => find (fun _ st=> st.`epk = x) cm = Some i =>
  hop4_key cm (z,x,y) = (if z = y ^ (oget cm.[i]).`esk then None else Some z,x,y).
proof. by move=> hc hf; rewrite /hop4_key /= (hop4_valid_find cm z x y i hc hf). qed.

local lemma hop4_key_injective cm u v:
  hop4_clients cm => hop4_key cm u = hop4_key cm v => u = v.
proof.
  by rewrite /hop4_clients /hop4_key /hop4_valid !hasP; smt(public_key_injective).
qed.

op hop4_ro (cm : (int, client_state) fmap)
           (rm : (pdh * pdh * pdh, sskey) fmap)
           (hm : (pdh option * pdh * pdh, sskey) fmap) =
  forall u, rm.[u] = hm.[hop4_key cm u].

local lemma hop4_ro_set cm rm hm u k:
  hop4_clients cm => hop4_ro cm rm hm =>
  hop4_ro cm rm.[u <- k] hm.[hop4_key cm u <- k].
proof.
  rewrite /hop4_ro=> hc hr v.
  have := hop4_key_injective cm u v hc.
  by rewrite !get_setE; smt().
qed.

local lemma hop4_ro_mem cm rm hm u:
  hop4_ro cm rm hm => (u \in rm <=> hop4_key cm u \in hm).
proof. by rewrite /hop4_ro !domE; smt(). qed.

op hop4_wf (cm : (int, client_state) fmap)
           (hm : (pdh option * pdh * pdh, sskey) fmap) =
  (forall z x y, hop4_valid cm z x y => hm.[Some z, x, y] = None) /\
  (forall x y, !has (fun _ st=> st.`epk = x) cm => hm.[None, x, y] = None).

local lemma hop4_wfE cm hm:
  hop4_wf cm hm =
  ((forall z x y, hop4_valid cm z x y => hm.[Some z,x,y] = None) /\
   (forall x y, !has (fun _ st=> st.`epk = x) cm => hm.[None,x,y] = None)).
proof. by rewrite /hop4_wf. qed.

local lemma hop4_wf_set cm hm u k:
  hop4_wf cm hm => hop4_wf cm hm.[hop4_key cm u <- k].
proof.
  rewrite /hop4_wf /hop4_key.
  case (hop4_valid cm u.`1 u.`2 u.`3)=> hu /=.
  + have hxu: has (fun _ st=> st.`epk = u.`2) cm
      by move: hu; rewrite /hop4_valid !hasP; smt().
    move=> [hs hn]; split.
    + by move=> z x y hv; rewrite get_setE /=; exact (hs z x y hv).
    + move=> x y hnx.
      have hx: x <> u.`2 by apply/negP=> hx; move: hnx; rewrite hx hxu.
      have nxy: (None<:pdh>,x,y) <> (None<:pdh>,u.`2,u.`3) by smt().
      by rewrite get_setE nxy /=; exact (hn x y hnx).
  + move=> [hs hn]; split.
    + move=> z x y hv; rewrite get_setE.
      by case ((Some z,x,y) = (Some u.`1,u.`2,u.`3))=> he /=; smt().
    + by move=> x y hnx; rewrite get_setE /=; exact (hn x y hnx).
qed.

op hop4_ro_inv (cm : (int, client_state) fmap)
           (rm : (pdh * pdh * pdh, sskey) fmap)
           (hm : (pdh option * pdh * pdh, sskey) fmap) =
  hop4_clients cm /\ hop4_ro cm rm hm /\ hop4_wf cm hm.

local lemma hop4_ro_invE cm rm hm:
  hop4_ro_inv cm rm hm = (hop4_clients cm /\ hop4_ro cm rm hm /\ hop4_wf cm hm).
proof. by rewrite /hop4_ro_inv. qed.

local lemma hop4_ro_inv_set cm rm hm u k:
  hop4_ro_inv cm rm hm =>
  hop4_ro_inv cm rm.[u <- k] hm.[hop4_key cm u <- k].
proof. by rewrite /hop4_ro_inv; smt(hop4_ro_set hop4_wf_set). qed.

op hop4_monitor (mm hm : (pdh option * pdh * pdh, sskey) fmap) =
  forall z x y, mm.[Some z, x, y] = hm.[Some z, x, y].

local lemma hop4_monitor_none mm hm x y k:
  hop4_monitor mm hm => hop4_monitor mm hm.[(None,x,y) <- k].
proof. by rewrite /hop4_monitor; smt(get_setE). qed.

local lemma hop4_monitor_some mm hm z x y k:
  hop4_monitor mm hm => hop4_monitor mm.[(Some z,x,y) <- k] hm.[(Some z,x,y) <- k].
proof. by rewrite /hop4_monitor; smt(get_setE). qed.

local lemma hop4_monitor_slot cm rm mm hm (u : pdh * pdh * pdh):
  hop4_ro_inv cm rm hm => hop4_monitor mm hm =>
  mm.[Some u.`1,u.`2,u.`3] = None \/ mm.[Some u.`1,u.`2,u.`3] = rm.[u].
proof.
  rewrite /hop4_ro_inv /hop4_wf /hop4_ro /hop4_monitor.
  move=> [hc [hr [hs hn]]] hmon.
  case (hop4_valid cm u.`1 u.`2 u.`3)=> hv.
  + left; by rewrite (hmon u.`1 u.`2 u.`3) (hs _ _ _ hv).
  + right; by rewrite (hmon u.`1 u.`2 u.`3) (hr u) /hop4_key hv /=.
qed.

local lemma hop4_monitor_miss cm rm mm hm u:
  hop4_ro_inv cm rm hm => hop4_monitor mm hm => u \notin rm =>
  mm.[Some u.`1,u.`2,u.`3] = None.
proof. by move=> hi hmon hx; have := hop4_monitor_slot cm rm mm hm u hi hmon; smt(domE). qed.

local lemma hop4_collision_respond_all cm rm hm x y:
  hop4_ro_inv cm rm hm =>
  (has (fun (u:pdh*pdh*pdh) _=> u.`2=x /\ u.`3=y) rm <=>
   has (fun (u:pdh option*pdh*pdh) _=> u.`2=x /\ u.`3=y) hm).
proof.
  rewrite /hop4_ro_inv /hop4_ro /hop4_wf !hasP.
  move=> [hc [hr [hs hn]]].
  split.
  + move=> [u k [hu [hx hy]]].
    exists (hop4_key cm u) k.
    split; first by rewrite -(hr u).
    by rewrite /hop4_key /=; smt().
  + move=> [u k [hu [hx hy]]].
    case (u.`1=None)=> htag.
    + have hslot: hm.[None,x,y]=Some k by smt().
      have hneg := hn x y.
      have hp: has (fun _ st=>st.`epk=x) cm by smt().
      move: hp; rewrite hasP.
      move=> [i st [hi he]].
      have hv: hop4_valid cm (y^st.`esk) x y.
      + rewrite /hop4_valid hasP; exists i st; smt().
      exists (y^st.`esk,x,y) k.
      by rewrite (hr (y^st.`esk,x,y)) /hop4_key /= hv /= hslot.
    + have [z hz]: exists z,u.`1=Some z by smt().
      have hslot:hm.[Some z,x,y]=Some k by smt().
      have hv:!hop4_valid cm z x y by smt().
      exists (z,x,y) k.
      by rewrite (hr (z,x,y)) /hop4_key /= hv /= hslot.
qed.

local equiv hop4_hprime_equiv:
  RO.get ~ Game4_b.Oracles.h':
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2} /\
    x{1}.`2 = x{2} /\ x{1}.`3 = y{2} /\ hop4_valid Exp_b.c_map{2} x{1}.`1 x{2} y{2}
    ==>
    ={res} /\ hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}.
proof.
  proc.
  case (x{1} \in RO.m{1}).
  + rcondf{1} 2; first by auto=> />.
    rcondf{2} 1; first by auto=> />; smt(hop4_ro_mem hop4_ro_invE).
    rnd{1}; auto=> />.
    by rewrite /hop4_ro /hop4_key; smt().
  + rcondt{1} 2; first by auto=> />.
    rcondt{2} 1; first by auto=> />; smt(hop4_ro_mem hop4_ro_invE).
    wp; rnd; auto=> />.
    move=> &1 &2 hc hr hs hn hm hv hx k hk.
    have hkey: hop4_key Exp_b.c_map{2} x{1} = (None,x{1}.`2,x{1}.`3).
    + by rewrite /hop4_key hv.
    have hi: hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2}.
    + by rewrite /hop4_ro_inv /hop4_wf.
    have hi' := hop4_ro_inv_set Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} x{1} k hi.
    rewrite hkey /hop4_ro_inv /hop4_wf in hi'.
    rewrite !get_set_sameE !oget_some /=.
    have [_ hi_rest] := hi'.
    split; first exact hi_rest.
    exact (hop4_monitor_none _ _ _ _ k hm).
qed.

local lemma hop4_valid_set cm i st z x y:
  i \notin cm =>
  (hop4_valid cm.[i <- st] z x y <=>
   hop4_valid cm z x y \/ (st.`epk = x /\ z = y ^ st.`esk)).
proof. by rewrite /hop4_valid !hasP; smt(get_setE domE). qed.

local lemma hop4_has_set (cm : (int, client_state) fmap) i st x:
  i \notin cm =>
  (has (fun _ st=> st.`epk = x) cm.[i <- st] <=>
   has (fun _ st=> st.`epk = x) cm \/ st.`epk = x).
proof. by rewrite !hasP; smt(get_setE domE). qed.

local lemma hop4_no_public_init (hm : (pdh option * pdh * pdh, sskey) fmap) x:
  !has (fun (u:pdh option * pdh * pdh) _=> u.`1 <> None /\ u.`2 = x) hm =>
  forall z y, hm.[Some z,x,y] = None.
proof. by rewrite hasP; smt(domE). qed.

local lemma hop4_collision_init mm hm x:
  hop4_monitor mm hm =>
  (has (fun (u:pdh option * pdh * pdh) _=> u.`1 <> None /\ u.`2 = x) mm <=>
   has (fun (u:pdh option * pdh * pdh) _=> u.`1 <> None /\ u.`2 = x) hm).
proof. by rewrite /hop4_monitor !hasP; smt(oget_some). qed.

local lemma hop4_new_same_value cm (i:int) st j st' y:
  hop4_clients cm => cm.[j] = Some st' => st.`esk \in dsk => st.`epk = g ^ st.`esk =>
  st.`epk = st'.`epk => y ^ st.`esk = y ^ st'.`esk.
proof. by rewrite /hop4_clients; smt(public_key_injective). qed.

local lemma hop4_ro_new_client cm rm hm i st:
  hop4_ro_inv cm rm hm => i \notin cm =>
  st.`esk \in dsk => st.`epk = g ^ st.`esk =>
  (forall z y, hm.[Some z,st.`epk,y] = None) =>
  hop4_ro_inv cm.[i <- st] rm hm.
proof.
  rewrite /hop4_ro_inv.
  move=> [hc [hr hw]] hi hs he hpub.
  split; first by apply hop4_clients_set.
  split.
  + rewrite /hop4_ro=> u.
    move: hr; rewrite /hop4_ro=> hr.
    have hu := hop4_valid_set cm i st u.`1 u.`2 u.`3 hi.
    rewrite /hop4_key.
    case (hop4_valid cm u.`1 u.`2 u.`3)=> hv.
    + have hvn: hop4_valid cm.[i <- st] u.`1 u.`2 u.`3 by smt().
      by rewrite hvn /= (hr u) /hop4_key hv /=.
    + case (st.`epk = u.`2 /\ u.`1 = u.`3 ^ st.`esk)=> hu'.
      + have hn: !has (fun _ st'=> st'.`epk = st.`epk) cm.
        + move: hv; rewrite /hop4_valid !hasP.
          rewrite /hop4_clients in hc; smt(public_key_injective).
        have hvn: hop4_valid cm.[i <- st] u.`1 u.`2 u.`3 by smt().
        have hx: st.`epk = u.`2 by smt().
        move: hw; rewrite /hop4_wf.
        move=> [hw1 hw2].
        rewrite hvn /= (hr u) /hop4_key hv /=.
        by rewrite -hx (hpub u.`1 u.`3) (hw2 st.`epk u.`3 hn).
      + have hvn: !hop4_valid cm.[i <- st] u.`1 u.`2 u.`3 by smt().
        by rewrite hvn /= (hr u) /hop4_key hv /=.
  + move: hw; rewrite /hop4_wf.
    move=> [hw1 hw2].
    split.
    + move=> z x y hv.
      have hvs := hop4_valid_set cm i st z x y hi.
      case (hop4_valid cm z x y)=> hv0.
      + exact (hw1 z x y hv0).
      + have hx: st.`epk = x by smt().
        by rewrite -hx; exact (hpub z y).
    + move=> x y hnx.
      have hh := hop4_has_set cm i st x hi.
      have hn: !has (fun _ st=> st.`epk = x) cm by smt().
      exact (hw2 x y hn).
qed.

op hop4_sessions n (cm : (int, client_state) fmap)
                    (pm : (int,int) fmap) (im : (int,pdh) fmap) =
  0 <= n /\ hop4_clients cm /\
  (forall i, i \in cm <=> 0 < i <= n) /\
  (forall i j, pm.[i] = Some j => i \in cm /\ im.[i] = Some (oget cm.[i]).`epk).

local lemma hop4_sessions_new n cm pm im st:
  hop4_sessions n cm pm im => st.`esk \in dsk => st.`epk = g ^ st.`esk =>
  hop4_sessions (n+1) cm.[n+1 <- st] pm im.
proof. by rewrite /hop4_sessions; smt(hop4_clients_set mem_set get_setE domE). qed.

local lemma hop4_sessions_partner n cm pm im i j:
  hop4_sessions n cm pm im => i \in cm =>
  hop4_sessions n cm pm.[i <- j] im.[i <- (oget cm.[i]).`epk].
proof. by rewrite /hop4_sessions; smt(get_setE). qed.

local lemma hop4_sessions_lookup n cm pm im i:
  hop4_sessions n cm pm im => 0 < i <= n =>
  i \in cm /\ (oget cm.[i]).`esk \in dsk /\ (oget cm.[i]).`epk = g ^ (oget cm.[i]).`esk.
proof. by rewrite /hop4_sessions /hop4_clients; smt(domE oget_some). qed.

local lemma hop4_receive_valid n cm pm im i y:
  hop4_sessions n cm pm im => 0 < i <= n =>
  hop4_valid cm (y ^ (oget cm.[i]).`esk) (oget cm.[i]).`epk y.
proof.
  move=> hs hi.
  have [hm _] := hop4_sessions_lookup n cm pm im i hs hi.
  rewrite /hop4_valid hasP /=.
  exists i (oget cm.[i]).
  by smt(domE oget_some).
qed.

local lemma hop4_respond_valid n cm pm im c j y:
  hop4_sessions n cm pm im => y \in dsk =>
  has (fun i j'=> j'=j /\ im.[i]=Some c) pm =>
  hop4_valid cm (c ^ y) c (g ^ y).
proof.
  rewrite /hop4_sessions.
  move=> [hn [hc [hd hp]]] hy.
  rewrite hasP /=.
  move=> [i j' [hj [he hi]]].
  have [hm hic] := hp i j' hj.
  have hpub: (oget cm.[i]).`epk = c by smt().
  have hcm: cm.[i] = Some (oget cm.[i]) by smt(domE oget_some).
  move: hc; rewrite /hop4_clients=> hc.
  have [hsk hpk] := hc i (oget cm.[i]) hcm.
  have hz: c ^ y = (g ^ y) ^ (oget cm.[i]).`esk.
  + by rewrite -hpub hpk; exact (shared_keyC _ _ hsk hy).
  rewrite /hop4_valid hasP /=.
  by exists i (oget cm.[i]); smt().
qed.

local lemma hop4_init_preserves n cm pm im rm mm hm pk x:
  hop4_sessions (n-1) cm pm im => hop4_ro_inv cm rm hm => hop4_monitor mm hm =>
  !has (fun (u:pdh option * pdh * pdh) _=> u.`1<>None /\ u.`2=g ^ x) mm => x \in dsk =>
  hop4_sessions n cm.[n <- {|pk=pk;epk=g ^ x;esk=x|}] pm im /\
  hop4_ro_inv cm.[n <- {|pk=pk;epk=g ^ x;esk=x|}] rm hm.
proof.
  move=> hses hri hmon hcoll hx.
  have hi: n \notin cm by move: hses; rewrite /hop4_sessions; smt().
  have he: n-1+1=n by smt().
  have hnocol: !has (fun (u:pdh option * pdh * pdh) _=> u.`1<>None /\ u.`2=g ^ x) hm.
  + have := hop4_collision_init mm hm (g ^ x) hmon; by smt().
  have hpub := hop4_no_public_init hm (g ^ x) hnocol.
  split.
  + have := hop4_sessions_new (n-1) cm pm im {|pk=pk;epk=g ^ x;esk=x|} hses hx _.
    + by trivial.
    by rewrite he.
  + exact (hop4_ro_new_client cm rm hm n {|pk=pk;epk=g ^ x;esk=x|} hri hi hx _ hpub).
qed.

local lemma hop4_sessionsE n cm pm im:
  hop4_sessions n cm pm im =
  (0 <= n /\ hop4_clients cm /\
   (forall i, (i \in cm => 0 < i /\ (0 < i => i <= n)) /\
              (0 < i => i <= n => i \in cm)) /\
   (forall i j, pm.[i]=Some j => i \in cm /\ im.[i]=Some (oget cm.[i]).`epk)).
proof. by rewrite /hop4_sessions; smt(). qed.

local module Hop4Cache = {
  include var Game4_b [-run]
  proc get(z x y : pdh): sskey = {
    var u, k;
    u <- hop4_key Exp_b.c_map (z,x,y);
    if (u \notin h_map) {
      k <$ dssk;
      h_map.[u] <- k;
    }
    return oget h_map.[u];
  }
}.

local equiv hop4_public_canonical:
  Game4_b.Oracles.h ~ Hop4Cache.get:
    ={arg, Exp_b.c_map, Game4_b.h_map} /\
    hop4_clients Exp_b.c_map{1} /\ hop4_wf Exp_b.c_map{1} Game4_b.h_map{1}
    ==> ={res, Exp_b.c_map, Game4_b.h_map}.
proof.
  proc; inline *.
  case ((Some z{1},x{1},y{1}) \in Game4_b.h_map{1}).
  + rcondf{1} 2; first by auto=> />.
    rcondf{2} 2; first by auto=> />; rewrite /hop4_key; smt(hop4_wfE domE).
    by auto=> />; rewrite /hop4_key; smt(hop4_wfE domE).
  + rcondt{1} 2; first by auto=> />.
    sp 2 1.
    match{1}.
    + rcondt{1} 1; first by auto=> />.
      rcondt{2} 1.
      + auto=> /> hf hc hs hn hm.
        have hf': find (fun _ st=> st.`epk = x{m}) Exp_b.c_map{m} = None by smt().
        by rewrite (hop4_key_none _ z{m} _ y{m} hf').
      wp; rnd; auto=> />.
      move=> &2 hf hc hs hn hm k hk.
      have hf': find (fun _ st=> st.`epk = x{2}) Exp_b.c_map{2} = None by smt().
      by rewrite (hop4_key_none _ z{2} _ y{2} hf') get_set_sameE oget_some.
    + sp 1 0.
      if{1}.
      + sp 2 0; if.
        + auto=> /> &1 &2 hf hc hs hn hm.
          have hf': find (fun _ st=> st.`epk = x{2}) Exp_b.c_map{2} = Some i{1} by smt().
          by rewrite (hop4_key_find _ (y{2} ^ (oget Exp_b.c_map{2}.[i{1}]).`esk) _ _ _ hc hf') /=.
        + rcondf{1} 5; first by auto=> />.
          wp; rnd; auto=> /> &1 &2 hf hc hs hn hm hmiss k hk.
          have hf': find (fun _ st=> st.`epk = x{2}) Exp_b.c_map{2} = Some i{1} by smt().
          by rewrite (hop4_key_find _ (y{2} ^ (oget Exp_b.c_map{2}.[i{1}]).`esk) _ _ _ hc hf') /=.
        + rcondf{1} 3; first by auto=> />.
          auto=> /> &1 &2 hf hc hs hn hm hmem.
          have hf': find (fun _ st=> st.`epk = x{2}) Exp_b.c_map{2} = Some i{1} by smt().
          by rewrite (hop4_key_find _ (y{2} ^ (oget Exp_b.c_map{2}.[i{1}]).`esk) _ _ _ hc hf') /=.
      + rcondt{1} 1; first by auto=> />.
        rcondt{2} 1.
        + auto=> /> hf hc hs hn hm hz.
          have hf': find (fun _ st=> st.`epk=x{m}) Exp_b.c_map{m}=Some i{m} by smt().
          by rewrite (hop4_key_find _ z{m} _ y{m} _ hc hf') hz /=.
        wp; rnd; auto=> /> &1 &2 hf hc hs hn hm hz k hk.
        have hf': find (fun _ st=> st.`epk=x{2}) Exp_b.c_map{2}=Some i{1} by smt().
        by rewrite (hop4_key_find _ z{2} _ y{2} _ hc hf') hz /= get_set_sameE oget_some.
qed.

local lemma hop4_monitor_relabel cm mm hm (u : pdh * pdh * pdh) k:
  hop4_monitor mm hm =>
  hop4_monitor (if hop4_valid cm u.`1 u.`2 u.`3 then mm else mm.[(Some u.`1,u.`2,u.`3) <- k])
               hm.[hop4_key cm u <- k].
proof.
  rewrite /hop4_key.
  case (hop4_valid cm u.`1 u.`2 u.`3)=> hv /=.
  + exact hop4_monitor_none.
  + exact hop4_monitor_some.
qed.

local lemma hop4_monitor_hit cm mm hm (u : pdh * pdh * pdh) k:
  hop4_monitor mm hm => hm.[hop4_key cm u] = Some k =>
  hop4_monitor (if hop4_valid cm u.`1 u.`2 u.`3 then mm else mm.[(Some u.`1,u.`2,u.`3) <- k]) hm.
proof.
  rewrite /hop4_key.
  case (hop4_valid cm u.`1 u.`2 u.`3)=> hv /=; first by smt().
  move=> hm0 hk.
  have hmk: mm.[Some u.`1,u.`2,u.`3] = Some k by move: hm0; rewrite /hop4_monitor; smt().
  by rewrite (FMap.get_set_id _ _ _ hmk).
qed.

local equiv hop4_cache_equiv (u : pdh * pdh * pdh):
  RO.get ~ Hop4Cache.get:
    arg{1} = u /\ arg{2} = u /\ hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}
    ==>
    ={res} /\ hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor
      (if hop4_valid Exp_b.c_map{2} u.`1 u.`2 u.`3 then Game4_b.h_map{1}
       else Game4_b.h_map{1}.[(Some u.`1,u.`2,u.`3) <- res{1}]) Game4_b.h_map{2} /\
    (Game4_b.h_map{1}.[Some u.`1,u.`2,u.`3] = None \/
     Game4_b.h_map{1}.[Some u.`1,u.`2,u.`3] = Some res{1}).
proof.
  proc.
  case (x{1} \in RO.m{1}).
  + rcondf{1} 2; first by auto=> />.
    rcondf{2} 2; first by auto=> />; smt(hop4_ro_mem hop4_ro_invE).
    rnd{1}; auto=> />.
    by rewrite /hop4_ro; smt(hop4_monitor_hit hop4_monitor_slot hop4_ro_invE hop4_wfE get_some oget_some).
  + rcondt{1} 2; first by auto=> />.
    rcondt{2} 2; first by auto=> />; smt(hop4_ro_mem hop4_ro_invE).
    wp; rnd; auto=> />.
    move=> &1 &2 hc hr hs hn hm hx k hk.
    rewrite !get_set_sameE !oget_some /=.
    have hi: hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2}.
    + by rewrite /hop4_ro_inv /hop4_wf.
    have hi' := hop4_ro_inv_set Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} (z{2},x{2},y{2}) k hi.
    rewrite /hop4_ro_inv /hop4_wf in hi'.
    have [_ hi_rest] := hi'.
    split; first exact hi_rest.
    split; first exact (hop4_monitor_relabel _ _ _ (z{2},x{2},y{2}) k hm).
    by left; exact (hop4_monitor_miss _ _ _ _ (z{2},x{2},y{2}) hi hm hx).
qed.

local equiv hop4_public_cache (u : pdh * pdh * pdh):
  Game35_b.Oracles.h ~ Hop4Cache.get:
    arg{1}=u /\ arg{2}=u /\ ={Exp_b.c_map} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}
    ==>
    ={res, Exp_b.c_map} /\ hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}.
proof.
  proc *; inline {1} 1.
  seq 5 1: (k{1}=r{2} /\ (z0{1},x0{1},y0{1})=u /\ valid_dh{1}=false /\
    ={Exp_b.c_map} /\ hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor
      (if hop4_valid Exp_b.c_map{2} u.`1 u.`2 u.`3 then Game4_b.h_map{1}
       else Game4_b.h_map{1}.[Some u.`1,u.`2,u.`3 <- k{1}]) Game4_b.h_map{2} /\
    (Game4_b.h_map{1}.[Some u.`1,u.`2,u.`3] = None \/
     Game4_b.h_map{1}.[Some u.`1,u.`2,u.`3] = Some k{1})).
  + call (hop4_cache_equiv u); auto=> />.
  + if{1}.
    + sp 1 0; match{1}.
      + rcondt{1} 1; first by auto=> />.
        auto=> /> &1 &2 hf hc hr hs hn hmon hslot hmiss.
        have hf': find (fun _ st=> st.`epk=x0{1}) Exp_b.c_map{2}=None by smt().
        have hv := hop4_valid_none Exp_b.c_map{2} z0{1} x0{1} y0{1} hf'.
        by move: hmon; rewrite hv /=.
      + sp 2 0; wp; auto=> /> &1 &2 hf hc hr hs hn hmon hslot hmiss.
        have hf': find (fun _ st=> st.`epk=x0{1}) Exp_b.c_map{2}=Some i{1} by smt().
        have hv := hop4_valid_find Exp_b.c_map{2} z0{1} x0{1} y0{1} i{1} hc hf'.
        by move: hmon; rewrite hv /=; case (z0{1}=y0{1} ^ (oget Exp_b.c_map{2}.[i{1}]).`esk)=> />.
    + auto=> /> &1 &2 hc hr hs hn hmon hslot hhit.
      have hlookup: Game4_b.h_map{1}.[Some z0{1},x0{1},y0{1}]=Some r{2} by smt(domE).
      by move: hmon; case (hop4_valid Exp_b.c_map{2} z0{1} x0{1} y0{1})=> /=;
        rewrite ?(FMap.get_set_id _ _ _ hlookup).
qed.

local equiv hop4_public_equiv (u : pdh * pdh * pdh):
  Game35_b.Oracles.h ~ Game4_b.Oracles.h:
    arg{1}=u /\ arg{2}=u /\ ={Exp_b.c_map} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}
    ==>
    ={res, Exp_b.c_map} /\ hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}.
proof.
  transitivity Hop4Cache.get
    (arg{1}=u /\ arg{2}=u /\ ={Exp_b.c_map} /\
     hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
     hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}
     ==>
     ={res, Exp_b.c_map} /\ hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
     hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2})
    (={arg, Exp_b.c_map, Game4_b.h_map} /\
     hop4_clients Exp_b.c_map{1} /\ hop4_wf Exp_b.c_map{1} Game4_b.h_map{1}
     ==> ={res, Exp_b.c_map, Game4_b.h_map})=> [/#|/#||].
  + exact (hop4_public_cache u).
  + by symmetry; conseq hop4_public_canonical=> />.
qed.

local lemma hop4_ro_ll: islossless RO.get.
proof. by proc; islossless. qed.
local lemma hop4_public25_ll: islossless Game35_b.Oracles.h.
proof. proc; inline *; islossless; match; islossless. qed.
local lemma hop4_public3_ll: islossless Game4_b.Oracles.h.
proof. proc; inline *; islossless; match; islossless. qed.

local equiv hop4_init_equiv:
  Game35_b.Oracles.init ~ Game4_b.Oracles.init:
    !Game4_b.bad_4{2} /\ ={arg} /\ ={glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}
    ==> if Game4_b.bad_4{2} then ={Game4_b.bad_4} else ={res} /\ ={glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}.
proof.
  proc.
  seq 2 2: (={pk, x, c, glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    !Game4_b.bad_4{2} /\ x{2} \in dsk /\ c{2}=g ^ x{2} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}).
  + by wp; rnd; auto=> />; smt().
  if.
  + by auto=> />.
  + by auto=> />.
  + conseq (_ : ={pk, x, c, glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    !Game4_b.bad_4{2} /\ x{2} \in dsk /\ c{2}=g ^ x{2} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2} ==> _) => //.
    swap{1} 1 1.
  if.
  + move=> &1 &2 hp.
    have hm: hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2} by smt().
    have he: c{1}=c{2} by smt().
    by rewrite he; exact (hop4_collision_init _ _ c{2} hm).
  + sp 4 2; match{1}; auto=> />.
  + sp 3 3; match =; auto=> />.
    + move=> &1 &2 cm n0 hf1 hf2 hbad hx hn hc hd hp hc2 hr hs hno hmon hcoll.
      have hses: hop4_sessions n0 cm Exp_b.p_map{2} Exp_b.i_map{2}.
      + by rewrite /hop4_sessions.
      have hri: hop4_ro_inv cm RO.m{1} Game4_b.h_map{2}.
      + by rewrite /hop4_ro_inv /hop4_wf.
      have [hns hnr] := hop4_init_preserves (n0+1) cm Exp_b.p_map{2} Exp_b.i_map{2} RO.m{1} Game4_b.h_map{1} Game4_b.h_map{2} pk{2} x{2} hses hri hmon hcoll hx.
      by rewrite -hop4_wfE -hop4_ro_invE -hop4_sessionsE; split; [exact hns|exact hnr].
    + move=> &1 &2 cm n0 hf1 hf2 hbad hx hn hc hd hp hc2 hr hs hno hmon hcoll.
      have hses: hop4_sessions n0 cm Exp_b.p_map{2} Exp_b.i_map{2}.
      + by rewrite /hop4_sessions.
      have hri: hop4_ro_inv cm RO.m{1} Game4_b.h_map{2}.
      + by rewrite /hop4_ro_inv /hop4_wf.
      have [hns hnr] := hop4_init_preserves (n0+1) cm Exp_b.p_map{2} Exp_b.i_map{2} RO.m{1} Game4_b.h_map{1} Game4_b.h_map{2} pk{2} x{2} hses hri hmon hcoll hx.
      have hi: (n0+1) \in cm.[n0+1 <- {|pk=pk{2};epk=g ^ x{2};esk=x{2}|}] by smt(mem_set).
      have hnp := hop4_sessions_partner _ _ _ _ (n0+1) j hns hi.
      rewrite get_set_sameE oget_some /= in hnp.
      by rewrite -hop4_wfE -hop4_ro_invE -hop4_sessionsE; split; [exact hnp|exact hnr].

qed.

local equiv hop4_respond_equiv:
  Game35_b.Oracles.respond ~ Game4_b.Oracles.respond:
    !Game4_b.bad_4{2} /\ ={arg} /\ ={glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}
    ==> if Game4_b.bad_4{2} then ={Game4_b.bad_4} else ={res} /\ ={glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}.
proof.
  proc; sp; if; auto; sp.
  seq 2 2: (={j, c, ch, r, y, h, glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    !Game4_b.bad_4{2} /\ y{2} \in dsk /\ h{2}=g ^ y{2} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}).
  + by wp; rnd; auto=> />.
  if.
  + move=> &1 &2 hp.
    have hi: hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} by smt(). (* HOP4: use the existing canonical cache relation to detect public and internal collisions together. *)
    have hec: c{1}=c{2} by smt().
    have heh: h{1}=h{2} by smt().
    by rewrite hec heh; exact (hop4_collision_respond_all _ _ _ c{2} h{2} hi). (* HOP4: synchronize the extended collision branch without a stronger invariant. *)
  + sp 1 1.
    seq 3 0: (Game4_b.bad_4{1} /\ Game4_b.bad_4{2}).
    + by wp; call{1} S_sign_ll; auto=> />.
    seq 1 0: (Game4_b.bad_4{1} /\ Game4_b.bad_4{2}).
    + if{1}.
      + by call{1} hop4_ro_ll; auto=> />.
      + by call{1} hop4_public25_ll; auto=> />.
    sp 1 0; match{1}.
    + by auto=> />.
    + sp 1 0; if{1}.
      + if{1}.
        + by wp; rnd{1}; auto=> />; smt(dssk_ll).
        + by auto=> />.
      + by auto=> />.
  + seq 2 2: (={j, c, ch, r, sk_j, y, h, sig, glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
      !Game4_b.bad_4{2} /\ y{2} \in dsk /\ h{2}=g ^ y{2} /\
      hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
      hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
      hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}).
    + by call (: true); auto=> />.
    sp 1 1.
    seq 1 1: (={j, c, ch, r, c', k, glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
      !Game4_b.bad_4{2} /\
      hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
      hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
      hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}).
    + if; auto.
      + call hop4_hprime_equiv; auto=> />.
        move=> &1 &2 hbad hy hn hc hd hp hc2 hr hs hno hm hpartner.
        have hses: hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2}.
        + by rewrite /hop4_sessions.
        exact (hop4_respond_valid _ _ _ _ c{2} j{2} y{2} hses hy hpartner).
      + exists* (c{1} ^ y{1}, c{1}, h{1}); elim*=> u.
        by call (hop4_public_equiv u); auto=> />.
    + sp 1 1; match =; auto=> />.
      sp 1 1; if; auto; if; auto.
qed.

local equiv hop4_receive_equiv:
  Game35_b.Oracles.receive ~ Game4_b.Oracles.receive:
    ={arg} /\ ={glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}
    ==> ={res} /\ ={glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}.
proof.
  proc; sp; if; auto.
  sp; if; auto; sp 1 1.
  seq 1 1: (={i, c, ch, st_i, h, sig, b, ko, glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    st_i{2}=oget Exp_b.c_map{2}.[i{2}] /\ 0<i{2}<=Exp_b.n{2} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}).
  + by auto=> />.
  seq 1 1: (={i, c, ch, ko, glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2}).
  + if; auto.
    wp; call hop4_hprime_equiv; auto=> />.
    move=> &1 &2 hi1 hi2 hn hc hd hp hc2 hr hs hno hm hb.
    have hi: 0<i{2}<=Exp_b.n{2} by smt().
    have hses: hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2}.
    + by rewrite /hop4_sessions.
    exact (hop4_receive_valid _ _ _ _ i{2} h{2} hses hi).
  + by auto=> />; smt(sub1set subset_fsetU_id fsetUC). (* HOP4: merging preserves ich because union with an existing member is idempotent. *)
qed.

local lemma hop4_init25_bad:
  phoare[Game35_b.Oracles.init: Game4_b.bad_4 ==> Game4_b.bad_4] = 1%r.
proof. by proc; auto=> />; smt(dsk_ll). qed.

local lemma hop4_init3_bad:
  phoare[Game4_b.Oracles.init: Game4_b.bad_4 ==> Game4_b.bad_4] = 1%r.
proof. by proc; auto=> />; smt(dsk_ll). qed.

local lemma hop4_respond25_bad:
  phoare[Game35_b.Oracles.respond: Game4_b.bad_4 ==> Game4_b.bad_4] = 1%r.
proof.
  proc; sp; if; auto; sp.
  seq 3: Game4_b.bad_4.
  + by auto=> />.
  + by auto=> />; smt(dsk_ll).
  + conseq (: true); inline *; islossless.
    + by match; islossless.
    + by match; islossless.
    + exact S_sign_ll.
  + by hoare; auto=> />.
  + by auto=> />.
qed.

local lemma hop4_respond3_bad:
  phoare[Game4_b.Oracles.respond: Game4_b.bad_4 ==> Game4_b.bad_4] = 1%r.
proof.
  proc; sp; if; auto; sp.
  seq 2: Game4_b.bad_4.
  + by auto=> />.
  + by auto=> />; smt(dsk_ll).
  + if; auto.
    conseq (: Game4_b.bad_4 ==> Game4_b.bad_4)=> //.
    conseq (: true); inline *; islossless.
    + by match; islossless.
    + by match; islossless.
    + exact S_sign_ll.
  + by hoare; auto=> />.
  + by auto=> />.
qed.

local lemma Hop4 b &m:
  `|Pr[Game3_b.run(b) @ &m: res] - Pr[Game4_b.run(b) @ &m: res]|
  <= Pr[Game4_b.run(b) @ &m: Game4_b.bad_4].
proof.
  have ->: Pr[Game3_b.run(b) @ &m: res] = Pr[Game35_b.run(b) @ &m: res].
  + byequiv (: ={glob A, glob S, b} ==> ={res})=> //; proc.
    call (: ={glob Exp_b, Game2_b.resp_inputs, glob S, glob RO, Game1_b.bad_1, Game3_b.bad_3});
      [1..3,6: by sim |4: by proc; inline *; sim; auto=> /> /#
       |7: by proc; inline *; wp; rnd; auto=> /> /#
       |8: by inline; auto=> /> /#].
    proc; sp; if; auto.
      seq 1 1: (={j,c,ch,r,glob Exp_b, Game2_b.resp_inputs,glob S,glob RO,Game1_b.bad_1,Game3_b.bad_3}).
      + by auto=> />.
      seq 3 4: (={j, c, ch, r, sk_j, y, h, glob Exp_b, Game2_b.resp_inputs, glob S, glob RO,
                   Game1_b.bad_1, Game3_b.bad_3}).
      + by auto=> /> /#.
      seq 1 1: (={j, c, ch, r, sk_j, y, h, sig, glob Exp_b, Game2_b.resp_inputs, glob S, glob RO,
                   Game1_b.bad_1, Game3_b.bad_3}).
      + by call (: true); auto.
      sp 1 1.
      seq 1 1: (={j, c, ch, r, c', k, glob Exp_b, Game2_b.resp_inputs, glob S, glob RO,
                   Game1_b.bad_1, Game3_b.bad_3}).
      + if{2}; by inline *; wp; rnd; auto=> /> /#.
      + by sim.
  byequiv: Game4_b.bad_4=> [||/#] //.
  proc.
  call (: Game4_b.bad_4,
    ={glob Exp_b, Game2_b.resp_inputs, glob S, Game1_b.bad_1, Game3_b.bad_3, Game4_b.bad_4} /\
    hop4_sessions Exp_b.n{2} Exp_b.c_map{2} Exp_b.p_map{2} Exp_b.i_map{2} /\
    hop4_ro_inv Exp_b.c_map{2} RO.m{1} Game4_b.h_map{2} /\
    hop4_monitor Game4_b.h_map{1} Game4_b.h_map{2},
    ={Game4_b.bad_4});
    [3,4: by move=> &hr *; proc; auto; call S_keygen_ll; auto=> />
     |5,8: by proc; auto=> />
     |6,7,9,10: by move=> &hr *; proc; auto
     |18,19: move=> &hr *; conseq (: true); proc; inline *; islossless].
  + exact A_ll.
  + by proc; auto; call (: true); auto=> />.
  + by conseq hop4_init_equiv=> />.
  + by move=> &2 bad; conseq hop4_init25_bad=> /> /#.
  + by move=> &1; conseq hop4_init3_bad=> /> /#.
  + by conseq hop4_respond_equiv=> /> /#.
  + by move=> &2 bad; conseq hop4_respond25_bad=> /> /#.
  + by move=> &1; conseq hop4_respond3_bad=> /> /#.
  + by conseq hop4_receive_equiv=> /> /#.
  + proc *; exists* (z{1},x{1},y{1}); elim*=> u.
    by call (hop4_public_equiv u); auto=> />.
  + by move=> &2 bad; proc *; call hop4_public25_ll; auto=> />.
  + by move=> &1; proc *; call hop4_public3_ll; auto=> />.
  inline; auto=> />; split.
  + by rewrite /hop4_clients /hop4_ro; smt(FMap.mem_empty FMap.emptyE).
  smt().
qed.


(* Abstract probability bound and lemma for Hop4 *)

op p_4: real.

local lemma Bad4 b &m:
  Pr[Game4_b.run(b) @ &m: Game4_b.bad_4] <= p_4 =>
  `|Pr[Game3_b.run(b) @ &m: res] - Pr[Game4_b.run(b) @ &m: res]| <= p_4.

proof.
  by move=> hp; exact (ler_trans _ _ _ (Hop4 b &m) hp).
qed.





(* Final reduction *)

(* Modules, definitions and proofs below by GPT-6.1-Sol. *)

local module CDHR = St_CDH(B2(S,A)).
local module SimR = B2(S,A,CDHR.Oracles).
local module ReductionTrace = {
  proc run():bool = {
    var r;
    St_CDH.win <- false;
    St_CDH.m <- 0;
    St_CDH.n <- 0;
    St_CDH.x_map <- empty;
    St_CDH.y_map <- empty;
    St_CDH.cr_1 <- fset0;
    St_CDH.cr_2 <- fset0;
    RO.init();
    Exp_b.b_ror <- witness;
    Exp_b.m <- 0;
    Exp_b.n <- 0;
    B2.n_x <- 0;
    B2.x_idx <- empty;
    B2.bad_2 <- false;
    Exp_b.q <- fset0;
    Exp_b.ich <- fset0;
    Exp_b.rch <- fset0;
    Exp_b.xp <- fset0;
    Exp_b.cr <- fset0;
    Exp_b.p_map <- empty;
    Exp_b.i_map <- empty;
    Exp_b.r_map <- empty;
    B2.resp_inputs <- fset0;
    Exp_b.pk_map <- empty;
    Exp_b.sk_map <- empty;
    Exp_b.c_map <- empty;
    B2.bad_1 <- false;
    B2.bad_3 <- false;
    B2.bad_4 <- false;
    B2.h_map <- empty;
    r <@ A(SimR.Oracles).distinguish();
    return r;
  }
}.

local lemma trace_win_equiv &m:
 Pr[ReductionTrace.run()@&m:St_CDH.win] = Pr[CDHR.run()@&m:res].
proof.
 byequiv (: ={glob A,glob S} ==> St_CDH.win{1}=res{2})=> //.
 by proc; inline SimR.solve RO.init; sp; sim. (* Apply sp first: B2.solve initialises in a different order. *)
qed.

local lemma cdh_ddh_keeps_win:
 hoare[CDHR.Oracles.ddh:St_CDH.win ==> St_CDH.win].
proof.
 proc; sp; if.
 + by auto=> />; smt().
 + sp; match; auto=> />; smt().
qed.

local lemma final_has_find ['a] (p:int -> 'a -> bool) (xm:(int,'a) fmap):
 has p xm => find p xm<>None.
proof. move=> hp; case(findP p xm)=> />; smt(hasP domE oget_some). qed.

local lemma ddh_correct_present (sx:sdh) (xm:(int,sdh) fmap) (y z:pdh):
 has (fun _ xi=>xi=sx) xm => z=y^sx =>
 find (fun _ xi=>g^sx=g^xi /\ z=y^xi) xm<>None.
proof. move=> hx hz; apply final_has_find; move:hx; rewrite !hasP; smt(). qed.

local lemma cdh_gen2_ll:islossless CDHR.Oracles.gen_2.
proof. proc; auto=> />; smt(dsk_ll). qed.

local lemma cdh_corrupt1_ll:islossless CDHR.Oracles.corrupt_1.
proof. proc; auto. qed.

local lemma cdh_ddh_ll:islossless CDHR.Oracles.ddh.
proof.
 proc; islossless; do ?(match; islossless).
qed.

local lemma b2_h_ll:islossless SimR.Oracles.h.
proof. proc; inline *; islossless; match; islossless; try match; islossless. qed.

local lemma b2_gen_ll:islossless SimR.Oracles.gen.
proof. proc; islossless; exact S_keygen_ll. qed.

local lemma b2_corrupt_ll:islossless SimR.Oracles.corrupt.
proof. proc; auto. qed.

local lemma b2_expose_ll:islossless SimR.Oracles.expose.
proof. proc; islossless; exact cdh_corrupt1_ll. qed.

local lemma b2_init_ll:islossless SimR.Oracles.init.
proof. proc; inline *; islossless; do ?(match; islossless). qed.

local lemma b2_respond_ll:islossless SimR.Oracles.respond.
proof.
 proc; inline *; islossless; try exact S_sign_ll; do ?(match; islossless).
qed.

local lemma b2_receive_ll:islossless SimR.Oracles.receive.
proof. proc; inline SimR.Oracles.h'; islossless. qed.

local lemma trace_ll:islossless ReductionTrace.run.
proof.
 proc; call (A_ll SimR.Oracles b2_gen_ll b2_corrupt_ll b2_expose_ll b2_init_ll b2_respond_ll b2_receive_ll b2_h_ll).
 inline RO.init; auto.
qed.

op red_erase (cm:(int,client_state) fmap) =
 map (fun _ st=>{|pk=st.`pk;epk=st.`epk;esk=witness;|}) cm.
local lemma red_erase_find cm x:
 find (fun _ st=>st.`epk=x) (red_erase cm) =
 find (fun _ st=>st.`epk=x) cm.
proof. by rewrite /red_erase find_map. qed.
local lemma red_erase_has cm (pm:(int,int) fmap) pk:
 has (fun i st=>st.`pk=pk /\ pm.[i]=None) (red_erase cm) =
 has (fun i st=>st.`pk=pk /\ pm.[i]=None) cm.
proof.
 by rewrite eq_iff /red_erase !hasP; smt(FMap.mapE get_some domE oget_some).
qed.

op red_protected (cm:(int,client_state) fmap) (ich:int fset) (ym:(int,sdh) fmap) x y =
 has (fun i st=>i \in ich /\ st.`epk=x) cm /\ has (fun _ sy=>g^sy=y) ym.
op red_cache (cm:(int,client_state) fmap) (ich:int fset) (ym:(int,sdh) fmap)
 (hl hr:(pdh option*pdh*pdh,sskey) fmap) =
 (forall (u:pdh option*pdh*pdh), u \in hl <=> u \in hr) /\
 (forall (u:pdh option*pdh*pdh), u.`1<>None \/ !red_protected cm ich ym u.`2 u.`3 => hl.[u]=hr.[u]) /\
 (forall (u:pdh option*pdh*pdh) i st, u \in hl => u.`1<>None => cm.[i]=Some st =>
   u.`2=st.`epk => oget u.`1<>u.`3^st.`esk).
op red_shape n m nx ny
 (cm:(int,client_state) fmap) (pm:(int,int) fmap) (im:(int,pdh) fmap) (pkm:(int,pkey) fmap)
 (idx:(int,int) fmap) (xm ym:(int,sdh) fmap) (xp ich cr1 cr2:int fset) =
 0<=n /\ 0<=m /\ 0<=nx /\ 0<=ny /\ cr2=fset0 /\
 (forall j pk, pkm.[j]=Some pk => 0<j<=m) /\
 (forall i, cm.[i]<>None <=> 0<i<=n) /\
 (forall i, idx.[i]<>None <=> 0<i<=n) /\
 (forall a sx, xm.[a]=Some sx => 0<a<=nx /\ sx \in dsk) /\
 (forall a sy, ym.[a]=Some sy => 0<a<=ny /\ sy \in dsk) /\
 (forall i st, cm.[i]=Some st =>
  0<oget idx.[i]<=nx /\ xm.[oget idx.[i]]=Some st.`esk /\ st.`epk=g^st.`esk) /\
 (forall i j sti stj, cm.[i]=Some sti => cm.[j]=Some stj => sti.`epk=stj.`epk => i=j) /\
 (forall i j, pm.[i]=Some j => 0<i<=n /\ 0<j<=m /\
   pkm.[j]=Some (oget cm.[i]).`pk /\ im.[i]=Some (oget cm.[i]).`epk) /\
 (forall i, i \in ich => 0<i<=n /\ i \notin xp /\ pm.[i]<>None) /\
 (forall i, i \in xp => 0<i<=n) /\
 (forall i, 0<i<=n => (oget idx.[i] \in cr1 <=> i \in xp)) /\
 (forall a, a \in cr1 => exists i, i \in xp /\ idx.[i]=Some a).

local abbrev red_inv bit (sl sr:glob S) (el er:glob Exp_b) (cdh:glob St_CDH)
 (nx:int) (idx:(int,int) fmap) (resp_l resp_r:pdh fset) (hl hr:(pdh option*pdh*pdh,sskey) fmap) =
 let (bl,cl,crl,il,ichl,ml,nl,pl,pkl,ql,rl,rchl,skl,xpl)=el in
 let (br,cr,crr,ir,ichr,mr,nr,pr,pkr,qr,rr,rchr,skr,xpr)=er in
 let (cr1,cr2,ny,native_n,win,xm,ym)=cdh in
 sl=sr /\ nl=nr /\ ml=mr /\ ql=qr /\ xpl=xpr /\ ichl=ichr /\ crl=crr /\
 resp_l=resp_r /\ pl=pr /\ il=ir /\ rl=rr /\ pkl=pkr /\ skl=skr /\
 bl=bit /\ cr=red_erase cl /\ native_n=nx /\
 red_shape nl ml native_n ny cl pl il pkl idx xm ym xpl ichl cr1 cr2 /\
 red_cache cl ichl ym hl hr.

local lemma red_shape_expose n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 i:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 0<i<=n => i \notin ich =>
 red_shape n m nx ny cm pm im pkm idx xm ym (xp `|` fset1 i) ich
   (cr1 `|` fset1 (oget idx.[i])) cr2.
proof.
 move=> hs hi hni.
 have hinj:forall a b,0<a<=n=>0<b<=n=>oget idx.[a]=oget idx.[b]=>a=b.
 + move=> a b ha hb hab.
   have hca:cm.[a]=Some (oget cm.[a]) by rewrite /red_shape in hs; smt(get_some domE).
   have hcb:cm.[b]=Some (oget cm.[b]) by rewrite /red_shape in hs; smt(get_some domE).
   rewrite /red_shape in hs; smt().
 rewrite /red_shape in hs; rewrite /red_shape; smt(in_fsetU in_fset1 get_some domE oget_some).
qed.

local lemma final_gen_state bit:
 equiv[Game4_b.Oracles.gen ~ SimR.Oracles.gen:
red_inv bit (glob S){1} (glob S){2}
 (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
 B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
 Game4_b.h_map{1} B2.h_map{2}
 ==> red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof.
 proc; seq 1 1:(red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={pk,sk}).
 + by call (:true); auto.
 + if.
   + auto=> />; move=> &1 &2.
     have he:=red_erase_has Exp_b.c_map{1} Exp_b.p_map{2} pk{2}.
     by smt().
   + by auto=> />.
   + auto=> />; smt(get_setE).
qed.

local lemma final_corrupt_state bit:
 equiv[Game4_b.Oracles.corrupt ~ SimR.Oracles.corrupt:
 ={arg} /\ red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2}
 ==> red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof. by proc; auto=> />. qed.

local lemma final_expose_state bit:
 equiv[Game4_b.Oracles.expose ~ SimR.Oracles.expose:
 ={arg} /\ red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2}
 ==> red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof.
 proc; inline CDHR.Oracles.corrupt_1; auto; move=> &1 &2 hs.
 have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
  Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
  B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
  St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
 case (0<i{1}<=Exp_b.n{1} /\ i{1} \notin Exp_b.ich{1})=> hi.
 + have hpos:0<i{1}<=Exp_b.n{1} by smt().
   have hnot:i{1} \notin Exp_b.ich{1} by smt().
   have he:=red_shape_expose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    i{1} hshape hpos hnot.
   have hst:Exp_b.c_map{1}.[i{1}]=Some (oget Exp_b.c_map{1}.[i{1}]).
   + rewrite /red_shape in hshape; smt(get_some domE).
   have hsecret:0<oget B2.x_idx{2}.[i{1}]<=St_CDH.n{2} /\
    St_CDH.x_map{2}.[oget B2.x_idx{2}.[i{1}]]=Some (oget Exp_b.c_map{1}.[i{1}]).`esk /\
    (oget Exp_b.c_map{1}.[i{1}]).`epk=g^(oget Exp_b.c_map{1}.[i{1}]).`esk.
   + rewrite /red_shape in hshape; smt().
   rewrite /red_erase in hs; smt(FMap.mapE oget_some).
 + by smt().
qed.

local lemma red_shape_gen1 n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 sx:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 => sx \in dsk =>
 red_shape n m (nx+1) ny cm pm im pkm idx xm.[nx+1<-sx] ym xp ich cr1 cr2.
proof. rewrite /red_shape => />; smt(get_setE). qed.

local lemma red_shape_cr1_bound n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 forall a,a \in cr1=>0<a<=nx.
proof.
 move=> hs a ha.
 have hex:exists i,i \in xp /\ idx.[i]=Some a by rewrite /red_shape in hs; smt().
 have [i [hxp hi]]:=hex.
 have hpos:0<i<=n by rewrite /red_shape in hs; smt().
 have hcm:cm.[i]=Some (oget cm.[i]) by rewrite /red_shape in hs; smt(get_some domE).
 rewrite /red_shape in hs; smt(oget_some).
qed.

local lemma red_shape_init_unregistered n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 sx pk:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 => sx \in dsk =>
 !has (fun _ st=>st.`epk=g^sx) cm =>
 red_shape (n+1) m (nx+1) ny cm.[n+1<-{|pk=pk;epk=g^sx;esk=sx|}]
  pm im pkm idx.[n+1<-nx+1] xm.[nx+1<-sx] ym xp ich cr1 cr2.
proof.
 move=> hs hsk hno.
 have hcr:=red_shape_cr1_bound n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 hs.
 rewrite hasP in hno.
 rewrite /red_shape in hs; rewrite /red_shape; progress; smt(get_setE oget_some).
qed.

local lemma red_protected_register cm ich ym i st x y:
 i \notin ich =>
 red_protected cm.[i<-st] ich ym x y=red_protected cm ich ym x y.
proof. rewrite /red_protected !hasP; smt(get_setE). qed.

local lemma red_cache_register cm ich ym hl hr i st:
 red_cache cm ich ym hl hr => i \notin ich =>
 !has (fun (u:pdh option*pdh*pdh) _=>u.`1<>None /\ u.`2=st.`epk) hl =>
 red_cache cm.[i<-st] ich ym hl hr.
proof.
 move=> hc hni hno.
 have hp:forall x y,red_protected cm.[i<-st] ich ym x y=red_protected cm ich ym x y
  by move=> x y; apply red_protected_register.
 rewrite hasP in hno; rewrite /red_cache in hc; rewrite /red_cache; progress; smt(get_setE).
qed.

local lemma red_shape_gen2 n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 sy:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 => sy \in dsk =>
 red_shape n m nx (ny+1) cm pm im pkm idx xm ym.[ny+1<-sy] xp ich cr1 cr2.
proof. rewrite /red_shape => />; smt(get_setE). qed.

local lemma cdh_query_wins:
 hoare[CDHR.Oracles.ddh:
  has (fun i xi=>x=g^xi /\ z=y^xi /\ i \notin St_CDH.cr_1) St_CDH.x_map /\
  has (fun j yj=>y=g^yj /\ j \notin St_CDH.cr_2) St_CDH.y_map
  ==> St_CDH.win].
proof.
 by proc; auto=> />; move=> &hr; rewrite !hasP; smt().
qed.

local lemma red_shape_protected_solution n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 x y z:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 has (fun i st=>i \in ich /\ st.`epk=x /\ z=y^st.`esk) cm =>
 has (fun _ sy=>g^sy=y) ym =>
 has (fun a sx=>x=g^sx /\ z=y^sx /\ a \notin cr1) xm /\
 has (fun a sy=>y=g^sy /\ a \notin cr2) ym.
proof.
 move=> hs hx hy; move:hx; rewrite hasP; move=> [i st [hi [hic [hx hz]]]].
 rewrite !hasP; split.
 + exists (oget idx.[i]) st.`esk; rewrite /red_shape in hs; smt().
 + move:hy; rewrite hasP; move=> [a sy [ha he]]; exists a sy.
   rewrite /red_shape in hs; smt(in_fset0).
qed.

local lemma red_shape_response_find n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 j c:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 find (fun i _=>pm.[i]=Some j /\ im.[i]=Some c) cm =
 find (fun i jj=>jj=j /\ im.[i]=Some c) pm.
proof.
 move=> hs; case (findP (fun i jj=>jj=j /\ im.[i]=Some c) pm).
 + move=> hn hnone; rewrite hn; apply find_eq_none.
   move=> a ha; rewrite /red_shape in hs; smt(domE oget_some).
 + move=> a jj hf hpm [hj him]; rewrite hf.
   have hpos:0<a<=n by rewrite /red_shape in hs; smt().
   have hcm:cm.[a]=Some (oget cm.[a]) by rewrite /red_shape in hs; smt(get_some domE).
   apply uniq_find_eq_some.
   + move=> b st hb [hpm_b him_b].
     have hst_b:st.`epk=c by rewrite /red_shape in hs; smt(oget_some).
     have hst_a:(oget cm.[a]).`epk=c by rewrite /red_shape in hs; smt(oget_some).
     rewrite /red_shape in hs; smt().
   + by rewrite domE hcm.
   + by smt().
qed.

local lemma red_cache_internal_set cm ich ym hl hr x y kl kr:
 red_cache cm ich ym hl hr =>
 (red_protected cm ich ym x y \/ kl=kr) =>
 red_cache cm ich ym hl.[(None,x,y)<-kl] hr.[(None,x,y)<-kr].
proof. rewrite /red_cache; progress; smt(get_setE mem_set). qed.

local lemma final_hprime_cache (cm:(int,client_state) fmap) (ich:int fset) (ym:(int,sdh) fmap) (x0 y0:pdh) (fresh:bool):
 equiv[Game4_b.Oracles.h' ~ SimR.Oracles.h':
  ={x,y} /\ x{1}=x0 /\ y{1}=y0 /\ red_cache cm ich ym Game4_b.h_map{1} B2.h_map{2} /\
  (fresh => (None,x0,y0) \notin Game4_b.h_map{1})
  ==> red_cache cm ich ym Game4_b.h_map{1} B2.h_map{2} /\
  (fresh \/ !red_protected cm ich ym x0 y0 => ={res})].
proof.
 proc; if.
 + auto; rewrite /red_cache; smt().
 + wp; rnd; skip; move=> &1 &2 hs k hk.
   have hh:=red_cache_internal_set cm ich ym Game4_b.h_map{1} B2.h_map{2} x0 y0 k k.
   smt(get_set_sameE).
 + skip; rewrite /red_cache; smt().
qed.

local lemma red_shape_challenge n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 i:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 0<i<=n => i \notin xp => pm.[i]<>None =>
 red_shape n m nx ny cm pm im pkm idx xm ym xp (ich `|` fset1 i) cr1 cr2.
proof. rewrite /red_shape; progress; smt(in_fsetU in_fset1). qed.

local lemma red_cache_challenge cm ich ym hl hr i:
 red_cache cm ich ym hl hr =>
 red_cache cm (ich `|` fset1 i) ym hl hr.
proof.
 rewrite /red_cache; progress.
 have hp:forall x y,red_protected cm ich ym x y =>
  red_protected cm (ich `|` fset1 i) ym x y
  by move=> x y; rewrite /red_protected !hasP; smt(in_fsetU in_fset1).
 smt().
qed.

local lemma red_shape_protected_client n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 i st y:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 cm.[i]=Some st => red_protected cm ich ym st.`epk y => i \in ich.
proof. rewrite /red_shape /red_protected !hasP; smt(). qed.

local lemma final_receive_state bit:
 equiv[Game4_b.Oracles.receive ~ SimR.Oracles.receive:
 ={arg} /\ red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2}
 ==> red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof.
 proc; sp; if.
 + by auto=> />.
 + sp; if.
   + by auto=> />.
   + sp 1 1; seq 1 1:(red_inv bit (glob S){1} (glob S){2}
    (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
    B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
    Game4_b.h_map{1} B2.h_map{2} /\ ={i,c,ch,h,sig,b} /\
 st_i{1}=oget Exp_b.c_map{1}.[i{1}] /\ st_i{2}=oget Exp_b.c_map{2}.[i{2}] /\
 0<i{1}<=Exp_b.n{1} /\ ko{1}=None /\ ko{2}=None /\
 (i{1} \in Exp_b.ich{1} => oget Exp_b.p_map{1}.[i{1}] \notin Exp_b.cr{1})).
     + auto=> />; rewrite /red_erase; smt(FMap.mapE get_some domE oget_some).
     + seq 1 1:(red_inv bit (glob S){1} (glob S){2}
      (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
      B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
      Game4_b.h_map{1} B2.h_map{2} /\ ={i,c,ch,h,sig,b} /\
 st_i{1}=oget Exp_b.c_map{1}.[i{1}] /\ st_i{2}=oget Exp_b.c_map{2}.[i{2}] /\
 0<i{1}<=Exp_b.n{1} /\ (ko{1}<>None <=> ko{2}<>None) /\
 (i{1} \notin Exp_b.ich{1} => ko{1}=ko{2}) /\
 (i{1} \in Exp_b.ich{1} => oget Exp_b.p_map{1}.[i{1}] \notin Exp_b.cr{1})).
       + if.
         + by auto=> />.
         + exists* Exp_b.c_map{1}; elim*=> cm0.
           exists* Exp_b.ich{1}; elim*=> ich0.
           exists* St_CDH.y_map{2}; elim*=> ym0.
           exists* st_i{1}.`epk; elim*=> x0.
           exists* h{1}; elim*=> y0.
           wp; call (final_hprime_cache cm0 ich0 ym0 x0 y0 false); auto; move=> &1 &2 hs.
           have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
            Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
            B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
            St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
           have hst:Exp_b.c_map{1}.[i{1}]=Some st_i{1}
            by rewrite /red_shape in hshape; smt(get_some domE).
           have hh:=red_shape_protected_client _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            i{1} st_i{1} h{1} hshape hst.
           rewrite /red_erase in hs; smt(FMap.mapE oget_some).
         + by auto=> />.
       + auto; move=> &1 &2 hs.
         have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
          Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
          B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
          St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
         have hcache:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} by smt().
         have hh:=red_shape_challenge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          i{1} hshape.
         have hc:=red_cache_challenge Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} i{1} hcache.
         have hguard:i{1} \in Exp_b.ich{1} =>
          i{1} \notin Exp_b.xp{1} /\ Exp_b.p_map{1}.[i{1}]<>None /\
          0<oget Exp_b.p_map{1}.[i{1}]<=Exp_b.m{1}.
         + move=> hi.
           have hj:Exp_b.p_map{1}.[i{1}]=Some (oget Exp_b.p_map{1}.[i{1}])
            by rewrite /red_shape in hshape; smt(get_some domE).
           rewrite /red_shape in hshape; smt().
         smt().
   + by auto=> />.
 + by auto=> />.
qed.

local lemma red_cache_has cm ich ym hl hr (p:pdh option*pdh*pdh -> bool):
 red_cache cm ich ym hl hr =>
 has (fun u _=>p u) hl=has (fun u _=>p u) hr.
proof.
 by rewrite /red_cache !hasP; smt(domE get_some).
qed.

local lemma red_erase_has_epk cm x:
 has (fun _ st=>st.`epk=x) (red_erase cm)=has (fun _ st=>st.`epk=x) cm.
proof.
 by rewrite eq_iff /red_erase !hasP; smt(FMap.mapE get_some domE oget_some).
qed.

local lemma red_shape_partner n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 i st j:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 cm.[i]=Some st => pkm.[j]=Some st.`pk =>
 red_shape n m nx ny cm pm.[i<-j] im.[i<-st.`epk] pkm idx xm ym xp ich cr1 cr2.
proof. rewrite /red_shape; progress; smt(get_setE oget_some). qed.

local lemma red_erase_register cm i st:
 red_erase cm.[i<-st]=(red_erase cm).[i<-{|pk=st.`pk;epk=st.`epk;esk=witness|}].
proof. by rewrite /red_erase map_set. qed.

local lemma final_init_state bit:
 equiv[Game4_b.Oracles.init ~ SimR.Oracles.init:
 !St_CDH.win{2} /\ ={arg} /\ red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2}
 ==> !St_CDH.win{2} => red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof.
 proc; inline CDHR.Oracles.gen_1.
 exists* St_CDH.n{2}; elim*=> nx0.
 exists* St_CDH.x_map{2}; elim*=> xm0.
 seq 2 5:(red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={c,pk} /\ c{1}=g^x{1} /\ x{1} \in dsk /\
 St_CDH.n{2}=nx0+1 /\ St_CDH.x_map{2}=xm0.[nx0+1<-x{1}] /\ red_shape Exp_b.n{1} Exp_b.m{1} nx0 St_CDH.m{2}
   Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
   B2.x_idx{2} xm0 St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
   St_CDH.cr_1{2} St_CDH.cr_2{2}).
 + wp; rnd; wp; skip; move=> &1 &2 hs nxnew sx hsk.
   have hshape:red_shape Exp_b.n{1} Exp_b.m{1} nx0 St_CDH.m{2}
   Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
   B2.x_idx{2} xm0 St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
   St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
   have he:=red_shape_gen1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    sx hshape hsk.
   smt().
 + if.
   + auto; move=> &1 &2 hs.
     have he:=red_erase_has_epk Exp_b.c_map{1} c{1}.
     have hcm:Exp_b.c_map{2}=red_erase Exp_b.c_map{1} by smt().
     have hr:B2.resp_inputs{2}=Game2_b.resp_inputs{1} by smt().
     have hc:c{2}=c{1} by smt().
     by rewrite hcm hr hc he.
   + by auto=> />.
   + if.
     + auto; move=> &1 &2 hs.
       have hc:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
        Game4_b.h_map{1} B2.h_map{2} by smt().
       have he:=red_cache_has Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
        Game4_b.h_map{1} B2.h_map{2}
        (fun (u:pdh option*pdh*pdh)=>u.`1<>None /\ u.`2=c{1}) hc.
       have hec:c{2}=c{1} by smt().
       rewrite hec; rewrite eq_iff in he; exact he.
     + by auto=> />.
     + seq 3 4:(red_inv bit (glob S){1} (glob S){2}
      (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
      B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
      Game4_b.h_map{1} B2.h_map{2} /\ ={c,pk,jo} /\
 Exp_b.c_map{1}.[Exp_b.n{1}]=Some {|pk=pk{1};epk=c{1};esk=x{1}|} /\
 jo{1}=find (fun _ pkj=>pkj=pk{1}) Exp_b.pk_map{1}).
       + wp; skip; move=> &1 &2 hs.
         have hshape:red_shape Exp_b.n{1} Exp_b.m{1} nx0 St_CDH.m{2}
          Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
          B2.x_idx{2} xm0 St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
          St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
         have hsk:x{1} \in dsk by smt().
         have hnproj:=red_erase_has_epk Exp_b.c_map{1} (g^x{1}).
         have hno:!has (fun _ st=>st.`epk=g^x{1}) Exp_b.c_map{1}.
         + have hc:c{1}=g^x{1} by smt().
           have hn:!has (fun _ st=>st.`epk=c{1}) Exp_b.c_map{1} by smt().
           by rewrite hc in hn.
         have he:=red_shape_init_unregistered _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          x{1} pk{1} hshape hsk hno.
         have hni:Exp_b.n{1}+1 \notin Exp_b.ich{1}
          by rewrite /red_shape in hshape; smt().
         have hcache:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} by smt().
         have hnc:!has (fun (u:pdh option*pdh*pdh) _=>u.`1<>None /\ u.`2=g^x{1})
          Game4_b.h_map{1}.
         + have hnL:!has (fun (u:pdh option*pdh*pdh) _=>u.`1<>None /\ u.`2=c{1})
            Game4_b.h_map{1} by smt().
           have hcc:c{1}=g^x{1} by smt().
           by rewrite -hcc.
         have hc:=red_cache_register Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} (Exp_b.n{1}+1)
          {|pk=pk{1};epk=g^x{1};esk=x{1}|} hcache hni hnc.
         have hp:=red_erase_register Exp_b.c_map{1} (Exp_b.n{1}+1)
          {|pk=pk{1};epk=g^x{1};esk=x{1}|}.
         have hnr:Exp_b.n{2}=Exp_b.n{1} by smt().
         have hcl:c{1}=g^x{1} by smt().
         have hcr:c{2}=g^x{1} by smt().
         have hpk:pk{2}=pk{1} by smt().
         have hnx:B2.n_x{2}=nx0+1 by smt().
         have hdn:St_CDH.n{2}=nx0+1 by smt().
         have hxm:St_CDH.x_map{2}=xm0.[nx0+1<-x{1}] by smt().
         have hproj:Exp_b.c_map{2}=red_erase Exp_b.c_map{1} by smt().
         have hpkm:Exp_b.pk_map{2}=Exp_b.pk_map{1} by smt().
         rewrite /= in hp.
         rewrite hnr hcl hcr hpk hnx hdn hxm hproj hpkm /= !get_set_sameE /=.
         smt().
       + match.
         + by auto=> />.
         + by auto=> />.
         + by auto=> />.
         + move=> j j0; wp; skip; move=> &1 &2 hs.
           have hfind:find (fun _ pkj=>pkj=pk{1}) Exp_b.pk_map{1}=Some j by smt().
           have [pk0 [hpkm heq]]:=find_some _ _ _ hfind.
           have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
            Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
            B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
            St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
           have hcm:Exp_b.c_map{1}.[Exp_b.n{1}]=Some {|pk=pk{1};epk=c{1};esk=x{1}|} by smt().
           have hp:Exp_b.pk_map{1}.[j]=Some pk{1} by smt().
           have he:=red_shape_partner _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Exp_b.n{1} {|pk=pk{1};epk=c{1};esk=x{1}|} j hshape hcm hp.
           rewrite /= in he; smt().
qed.

local lemma ddh_known_x_win (sx:sdh) (y0 z0:pdh) (trigger:bool):
 hoare[CDHR.Oracles.ddh:
   x=g^sx /\ y=y0 /\ z=z0 /\ sx \in dsk /\
   has (fun _ xi=>xi=sx) St_CDH.x_map /\
   (forall i xi, St_CDH.x_map.[i]=Some xi => xi \in dsk) /\
   (forall j yj, St_CDH.y_map.[j]=Some yj => yj \in dsk)
   /\ (trigger =>
    has (fun i xi=>g^sx=g^xi /\ z0=y0^xi /\ i \notin St_CDH.cr_1) St_CDH.x_map /\
    has (fun j yj=>y0=g^yj /\ j \notin St_CDH.cr_2) St_CDH.y_map)
   ==> res=(z0=y0^sx) /\ (trigger => St_CDH.win)].
proof.
 proc; sp; if.
 + by auto=> />; move=> &hr; rewrite !hasP; smt(public_key_injective).
 + sp; match.
   + by auto=> />; move=> &hr; rewrite !hasP; smt().
   + auto=> />; move=> &hr hj hs hx hxm hym hw hn.
     have hfj:find (fun _ yj=>y0=g^yj) St_CDH.y_map{hr}=Some j{hr} by smt().
     have [yj [hjy hy]]:=find_some _ _ _ hfj.
     have hc:=shared_keyC sx yj hs (hym j{hr} yj hjy).
     by move:hn hx hw; rewrite !hasP; smt(oget_some).
qed.

local lemma ddh_known_x_win_ph (sx:sdh) (y0 z0:pdh) (trigger:bool):
 phoare[CDHR.Oracles.ddh:
   x=g^sx /\ y=y0 /\ z=z0 /\ sx \in dsk /\
   has (fun _ xi=>xi=sx) St_CDH.x_map /\
   (forall i xi, St_CDH.x_map.[i]=Some xi => xi \in dsk) /\
   (forall j yj, St_CDH.y_map.[j]=Some yj => yj \in dsk) /\
   (trigger =>
    has (fun i xi=>g^sx=g^xi /\ z0=y0^xi /\ i \notin St_CDH.cr_1) St_CDH.x_map /\
    has (fun j yj=>y0=g^yj /\ j \notin St_CDH.cr_2) St_CDH.y_map)
   ==> res=(z0=y0^sx) /\ (trigger => St_CDH.win)]=1%r.
proof. conseq cdh_ddh_ll (ddh_known_x_win sx y0 z0 trigger)=> //. qed.

local lemma red_cache_public_set cm ich ym hl hr z x y k:
 red_cache cm ich ym hl hr =>
 (forall i st,cm.[i]=Some st => x=st.`epk => z<>y^st.`esk) =>
 red_cache cm ich ym hl.[(Some z,x,y)<-k] hr.[(Some z,x,y)<-k].
proof. rewrite /red_cache; progress; smt(get_setE mem_set). qed.

local lemma red_shape_h_pre n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 i st y z:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 cm.[i]=Some st =>
 st.`epk=g^st.`esk /\ st.`esk \in dsk /\
 has (fun _ sx=>sx=st.`esk) xm /\
 (forall a sx,xm.[a]=Some sx=>sx \in dsk) /\
 (forall a sy,ym.[a]=Some sy=>sy \in dsk) /\
 (red_protected cm ich ym st.`epk y /\ z=y^st.`esk =>
  has (fun a sx=>g^st.`esk=g^sx /\ z=y^sx /\ a \notin cr1) xm /\
  has (fun a sy=>y=g^sy /\ a \notin cr2) ym).
proof.
 move=> hs hcm.
 have hx:xm.[oget idx.[i]]=Some st.`esk /\ st.`epk=g^st.`esk
  by rewrite /red_shape in hs; smt().
 have hpub:st.`epk=g^st.`esk by smt().
 have hhas:has (fun _ sx=>sx=st.`esk) xm
  by rewrite hasP; exists (oget idx.[i]) st.`esk; smt().
 have hgood:st.`esk \in dsk /\
  (forall a sx,xm.[a]=Some sx=>sx \in dsk) /\
  (forall a sy,ym.[a]=Some sy=>sy \in dsk)
  by rewrite /red_shape in hs; smt().
 split; first by smt().
split; first by smt().
split; first by smt().
split; first by smt().
split; first by smt().
 move=> [hp hz].
 have hi:=red_shape_protected_client n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 i st y hs hcm hp.
 have hc:has (fun a st0=>a \in ich /\ st0.`epk=st.`epk /\ z=y^st0.`esk) cm
  by rewrite hasP; exists i st; smt().
 have hy:has (fun _ sy=>g^sy=y) ym by rewrite /red_protected in hp; smt().
 have hw:=red_shape_protected_solution n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 st.`epk y z hs hc hy.
 by rewrite hpub in hw.
qed.

local lemma final_h_state bit:
 equiv[Game4_b.Oracles.h ~ SimR.Oracles.h:
 !St_CDH.win{2} /\ ={arg} /\ red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2}
 ==> !St_CDH.win{2} => red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof.
 proc; sp 1 1; if.
 + auto; rewrite /red_cache; smt().
 + sp 1 0; match{1}.
   + seq 0 1:(red_inv bit (glob S){1} (glob S){2}
    (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
    B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
    Game4_b.h_map{1} B2.h_map{2} /\ ={z,x,y} /\ ko{1}=None /\ ko{2}=None /\
     find (fun _ st=>st.`epk=x{1}) Exp_b.c_map{1}=None).
     + call{2} cdh_ddh_ll; auto=> />; smt().
     + rcondf{2} 1.
       + move=> &m; auto; move=> &hr hs.
         have hp:=red_erase_has_epk Exp_b.c_map{m} x{m}.
         have hc:Exp_b.c_map{hr}=red_erase Exp_b.c_map{m} by smt().
         have hx:x{hr}=x{m} by smt().
         have hn:!has (fun _ st=>st.`epk=x{m}) Exp_b.c_map{m}.
         + have hh:=final_has_find (fun _ st=>st.`epk=x{m}) Exp_b.c_map{m}; smt().
         by rewrite hc hx hp hn.
       + rcondt{1} 1; first by move=> &m; auto=> />.
         wp; rnd; skip; move=> &1 &2 hs k hk.
         have hc:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} by smt().
         have hn:forall a st,Exp_b.c_map{1}.[a]=Some st=>x{1}=st.`epk=>z{1}<>y{1}^st.`esk.
         + have hh:=final_has_find (fun _ st=>st.`epk=x{1}) Exp_b.c_map{1}.
           rewrite hasP in hh; smt().
         have he:=red_cache_public_set Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} z{1} x{1} y{1} k hc hn.
         smt(oget_some).
   + sp 1 0.
     exists* st_i{1}; elim*=> st0.
     exists* y{1}; elim*=> y0.
     exists* z{1}; elim*=> z0.
     exists* Exp_b.c_map{1}; elim*=> cm0.
     exists* Exp_b.ich{1}; elim*=> ich0.
     exists* St_CDH.y_map{2}; elim*=> ym0.
     seq 0 1:(red_inv bit (glob S){1} (glob S){2}
      (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
      B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
      Game4_b.h_map{1} B2.h_map{2} /\ ={z,x,y} /\ ko{1}=None /\ ko{2}=None /\
      st_i{1}=st0 /\ Exp_b.c_map{1}=cm0 /\ Exp_b.ich{1}=ich0 /\ St_CDH.y_map{2}=ym0 /\
      y{1}=y0 /\ z{1}=z0 /\ x{1}=st0.`epk /\ Exp_b.c_map{1}.[i{1}]=Some st0 /\
      b{2}=(z0=y0^st0.`esk) /\
      (red_protected cm0 ich0 ym0 st0.`epk y0 /\ b{2} => St_CDH.win{2})).
     + call{2} (ddh_known_x_win_ph st0.`esk y0 z0
        (red_protected cm0 ich0 ym0 st0.`epk y0 /\ z0=y0^st0.`esk)).
       auto; move=> &1 &2 hs.
       have hf:find (fun _ st=>st.`epk=x{1}) Exp_b.c_map{1}=Some i{1} by smt().
       have [st [hcm hx]]:=find_some _ _ _ hf.
       have hst:st=st0 by smt(oget_some).
       have hs0:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
        Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
        B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
        St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
       have hcs:Exp_b.c_map{1}.[i{1}]=Some st0 by smt().
       have hd:=red_shape_h_pre Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
        Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
        B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
        St_CDH.cr_1{2} St_CDH.cr_2{2} i{1} st0 y0 z0 hs0 hcs.
       smt().
     + if.
       + auto; move=> &1 &2 hs.
         have hp:=red_erase_has_epk Exp_b.c_map{1} x{1}.
         have hh:has (fun _ st=>st.`epk=x{1}) Exp_b.c_map{1}
          by rewrite hasP; exists i{1} st0; smt().
         have hc:Exp_b.c_map{2}=red_erase Exp_b.c_map{1} by smt().
         have hx:x{2}=x{1} by smt().
         rewrite hc hx hp hh /=; smt().
       + seq 2 2:(red_inv bit (glob S){1} (glob S){2}
        (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
        B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
        Game4_b.h_map{1} B2.h_map{2} /\ ko{1}<>None /\
          (!St_CDH.win{2} => ko{1}=ko{2})).
         + wp; call (final_hprime_cache cm0 ich0 ym0 (st0.`epk) y0 false).
           auto; move=> &1 &2 hs; smt(oget_some).
         + rcondf{1} 1; first by move=> &m; auto=> />.
           by auto=> />; smt().
       + rcondt{1} 1; first by move=> &m; auto=> />.
         wp; rnd; skip; move=> &1 &2 hs k hk.
         have hc:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} by smt().
         have hn:forall a st,Exp_b.c_map{1}.[a]=Some st=>x{1}=st.`epk=>z{1}<>y{1}^st.`esk.
         + have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
            Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
            B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
            St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
           rewrite /red_shape in hshape; smt().
         have he:=red_cache_public_set Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
          Game4_b.h_map{1} B2.h_map{2} z{1} x{1} y{1} k hc hn.
         smt(oget_some).

 + auto; rewrite /red_cache; smt().
qed.

local lemma red_cache_gen2 cm ich ym hl hr a sy:
 red_cache cm ich ym hl hr => ym.[a]=None =>
 red_cache cm ich ym.[a<-sy] hl hr.
proof.
 move=> hc ha.
 have hp:forall x y,red_protected cm ich ym x y=>red_protected cm ich ym.[a<-sy] x y.
 + move=> x y; rewrite /red_protected !hasP; smt(get_setE).
 rewrite /red_cache in hc; rewrite /red_cache; progress; smt().
qed.

local lemma red_protected_response_pair cm ich ym i st a sy:
 cm.[i]=Some st => ym.[a]=Some sy =>
 red_protected cm (ich `|` fset1 i) ym st.`epk (g^sy).
proof. rewrite /red_protected !hasP; smt(in_fsetU in_fset1). qed.

local module FinalResponseKeys = {
 proc random(x:pdh,y:pdh):sskey={
  var cachek,k;
  cachek <$ dssk;
  Game4_b.h_map.[None,x,y] <- cachek;
  k <$ dssk;
  return k;
 }

 proc real(x:pdh,y:pdh):sskey={
  var cachek,k;
  cachek <$ dssk;
  B2.h_map.[None,x,y] <- cachek;
  k <- oget B2.h_map.[None,x,y];
  return k;
 }
}.

local lemma final_response_key_readback cm ich ym x0 y0:
 equiv[FinalResponseKeys.random ~ FinalResponseKeys.real:
  ={x,y} /\ x{1}=x0 /\ y{1}=y0 /\
  red_cache cm ich ym Game4_b.h_map{1} B2.h_map{2} /\
  red_protected cm ich ym x0 y0
  ==> red_cache cm ich ym Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof.
 proc.
 exists* Game4_b.h_map{1}; elim*=> hl0.
 exists* B2.h_map{2}; elim*=> hr0.
 seq 2 0:(={x,y} /\ x{1}=x0 /\ y{1}=y0 /\
  Game4_b.h_map{1}=hl0.[(None,x0,y0)<-cachek{1}] /\ B2.h_map{2}=hr0 /\
  red_cache cm ich ym hl0 hr0 /\ red_protected cm ich ym x0 y0).
 + wp; rnd{1}; skip=> />; smt(dssk_ll).
 + wp; rnd; skip; move=> &1 &2 hs k hk.
   have hc:red_cache cm ich ym hl0 hr0 by smt().
   have hp:red_protected cm ich ym x0 y0 \/ cachek{1}=k by smt().
   have hh:=red_cache_internal_set cm ich ym hl0 hr0 x0 y0 cachek{1} k hc hp.
   have hx:x{2}=x0 by smt().
   have hy:y{2}=y0 by smt().
   have hr:B2.h_map{2}=hr0 by smt().
   rewrite hx hy hr /= !get_set_sameE /=; smt().
qed.

local lemma red_shape_response_challenge n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 j c i a sy:
 red_shape n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 =>
 find (fun v _=>pm.[v]=Some j /\ im.[v]=Some c) cm=Some i =>
 i \notin xp => ym.[a]=Some sy =>
 red_shape n m nx ny cm pm im pkm idx xm ym xp (ich `|` fset1 i) cr1 cr2 /\
 red_protected cm (ich `|` fset1 i) ym c (g^sy).
proof.
 move=> hs hf hxp hy.
 have [st [hcm [hpm him]]]:=find_some _ _ _ hf.
 have hi:0<i<=n by rewrite /red_shape in hs; smt().
 have hp:pm.[i]<>None by smt().
 have hc:st.`epk=c by rewrite /red_shape in hs; smt(oget_some).
 have hh:=red_shape_challenge n m nx ny cm pm im pkm idx xm ym xp ich cr1 cr2 i hs hi hxp hp.
 have hprot:=red_protected_response_pair cm ich ym i st a sy hcm hy.
 rewrite hc in hprot; smt().
qed.

local lemma red_pair_fresh (hl:(pdh option*pdh*pdh,sskey) fmap) (x y:pdh):
 !has (fun (u:pdh option*pdh*pdh) _=>u.`2=x /\ u.`3=y) hl =>
 forall (z:pdh option),(z,x,y) \notin hl.
proof.
 by rewrite hasP=> hn z; smt(domE get_some).
qed.

local lemma final_no_has_find ['a] (p:int -> 'a -> bool) (m:(int,'a) fmap):
 !has p m => find p m=None.
proof.
 by case (findP p m)=> />; rewrite hasP; smt().
qed.

local lemma final_respond_state bit:
 equiv[Game4_b.Oracles.respond ~ SimR.Oracles.respond:
 !St_CDH.win{2} /\ ={arg} /\ red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2}
 ==> !St_CDH.win{2} => red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={res}].
proof.
 proc; sp 1 1; if.
 + by auto=> />.
 + seq 1 1:(red_inv bit (glob S){1} (glob S){2}
    (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
    B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2} Game4_b.h_map{1} B2.h_map{2} /\
    !St_CDH.win{2} /\ ={j,c,ch,r} /\ r{1}=None /\ 0<j{1}<=Exp_b.m{1}).
   + by auto=> /> /#.
   exists* St_CDH.m{2}; elim*=> ny0.
   exists* St_CDH.y_map{2}; elim*=> ym0.
   seq 2 2:(red_inv bit (glob S){1} (glob S){2}
    (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
    B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
    Game4_b.h_map{1} B2.h_map{2} /\ !St_CDH.win{2} /\ ={j,c,ch,h,r} /\ r{1}=None /\
    y{1} \in dsk /\ h{1}=g^y{1} /\
    (has (fun i jj=>jj=j{1} /\ Exp_b.i_map{1}.[i]=Some c{1}) Exp_b.p_map{1} =>
       St_CDH.y_map{2}.[St_CDH.m{2}]=Some y{1}) /\
    (!has (fun i jj=>jj=j{1} /\ Exp_b.i_map{1}.[i]=Some c{1}) Exp_b.p_map{1} => y{2}=y{1})).
   + sp 0 1; if{2}.
     + inline CDHR.Oracles.gen_2; wp; rnd; wp; skip; move=> &1 &2 hs nynew sy hsy.
       have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} ny0
        Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
        B2.x_idx{2} St_CDH.x_map{2} ym0 Exp_b.xp{1} Exp_b.ich{1}
        St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
       have he:=red_shape_gen2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        sy hshape hsy.
       have hnone:ym0.[ny0+1]=None by rewrite /red_shape in hshape; smt(get_some domE).
       have hc:red_cache Exp_b.c_map{1} Exp_b.ich{1} ym0 Game4_b.h_map{1} B2.h_map{2} by smt().
       have hh:=red_cache_gen2 Exp_b.c_map{1} Exp_b.ich{1} ym0
        Game4_b.h_map{1} B2.h_map{2} (ny0+1) sy hc hnone.
       have hpm:Exp_b.p_map{1}=Exp_b.p_map{2} by smt().
       have him:Exp_b.i_map{1}=Exp_b.i_map{2} by smt().
       have hj:j{1}=j{2} by smt().
       have hcc:c{1}=c{2} by smt().
       have hyn:nynew=ny0+1 by smt().
       have hym:St_CDH.y_map{2}=ym0 by smt().
       rewrite hpm him hj hcc hyn hym /=; smt(get_set_sameE).
     + wp; rnd; wp; skip; move=> &1 &2 hs sy hsy.
       have hpm:Exp_b.p_map{1}=Exp_b.p_map{2} by smt().
       have him:Exp_b.i_map{1}=Exp_b.i_map{2} by smt().
       have hj:j{1}=j{2} by smt().
       have hcc:c{1}=c{2} by smt().
       rewrite hpm him hj hcc /=; smt().
   + if.
     + auto; move=> &1 &2 hs.
       have hc:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
        Game4_b.h_map{1} B2.h_map{2} by smt().
       have hh:=red_cache_has Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
        Game4_b.h_map{1} B2.h_map{2} (fun (u:pdh option*pdh*pdh)=>u.`2=c{1} /\ u.`3=h{1}) hc.
       have hc2:c{2}=c{1} by smt().
       have hh2:h{2}=h{1} by smt().
       rewrite eq_iff in hh; rewrite hc2 hh2; exact hh.
     + by auto=> />; smt().
     + seq 2 2:(red_inv bit (glob S){1} (glob S){2}
      (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
      B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
      Game4_b.h_map{1} B2.h_map{2} /\ !St_CDH.win{2} /\ ={j,c,ch,h,r,sig} /\ r{1}=None /\
       y{1} \in dsk /\ h{1}=g^y{1} /\
       !has (fun (u:pdh option*pdh*pdh) _=>u.`2=c{1} /\ u.`3=h{1}) Game4_b.h_map{1} /\
       (has (fun i jj=>jj=j{1} /\ Exp_b.i_map{1}.[i]=Some c{1}) Exp_b.p_map{1} =>
          St_CDH.y_map{2}.[St_CDH.m{2}]=Some y{1}) /\
       (!has (fun i jj=>jj=j{1} /\ Exp_b.i_map{1}.[i]=Some c{1}) Exp_b.p_map{1} => y{2}=y{1})).
       + call (:true); auto=> />; smt().
       + sp 1 1; if.
         + auto=> />.
         + swap{1} 2 -1; swap{2} 2 -1.
           seq 1 1:(red_inv bit (glob S){1} (glob S){2}
            (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
            B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
            Game4_b.h_map{1} B2.h_map{2} /\ !St_CDH.win{2} /\ ={j,c,ch,h,r,sig,c',io} /\
            io{1}<>None /\ r{1}=None /\
            io{1}=find (fun a _=>Exp_b.p_map{1}.[a]=Some j{1} /\ Exp_b.i_map{1}.[a]=Some c{1}) Exp_b.c_map{1} /\
            io{2}=find (fun a jj=>jj=j{2} /\ Exp_b.i_map{2}.[a]=Some c{2}) Exp_b.p_map{2} /\
            c'{1}=(h{1},sig{1}) /\ y{1} \in dsk /\ h{1}=g^y{1} /\
            St_CDH.y_map{2}.[St_CDH.m{2}]=Some y{1} /\
            !has (fun (u:pdh option*pdh*pdh) _=>u.`2=c{1} /\ u.`3=h{1}) Game4_b.h_map{1}).
           + auto; move=> &1 &2 hs.
             have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
              Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
              B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
              St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
             have he:=red_shape_response_find _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              j{1} c{1} hshape.
             have hhas:has (fun a jj=>jj=j{1} /\ Exp_b.i_map{1}.[a]=Some c{1}) Exp_b.p_map{1} by smt().
             have hn:=final_has_find _ _ hhas.
             have hpm:Exp_b.p_map{2}=Exp_b.p_map{1} by smt().
             have him:Exp_b.i_map{2}=Exp_b.i_map{1} by smt().
             have hj:j{2}=j{1} by smt().
             have hcc:c{2}=c{1} by smt().
             have hymn:St_CDH.y_map{2}.[St_CDH.m{2}]=Some y{1} by smt().
             have hmsg:c'{1}=c'{2} by move: hs=> />.
             rewrite hpm him hj hcc /= he.
             smt().
           + match Some{1} 2.
             + move=> &m; wp; call (:true); auto=> />; smt(some_oget).
             + match Some{2} 2.
               + move=> &m; wp; call (:true); auto=> />; smt(some_oget).
               + case (ch{1} /\ i{1} \notin Exp_b.xp{1}).
                 + rcondt{1} 3.
                   + move=> &m; wp; call (:true); auto=> />; smt().
                   + rcondt{2} 3.
                     + move=> &m; wp; call (:true); auto=> />; smt().
                     + case bit.
                       + rcondt{1} 3.
                         + move=> &m; wp; call (:true); auto=> />; smt().
                         + swap{1} 2 -1; swap{2} 2 -1; sp 1 1.
                           inline Game4_b.Oracles.h' SimR.Oracles.h'; sp 2 2.
                           rcondt{1} 1.
                           + move=> &m; auto; move=> &hr hs.
                             have hn:!has (fun (u:pdh option*pdh*pdh) _=>u.`2=c{hr} /\ u.`3=h{hr}) Game4_b.h_map{hr} by smt().
                             have hf:=red_pair_fresh Game4_b.h_map{hr} c{hr} h{hr} hn None.
                             have hx:x{hr}=c{hr} by smt().
                             have hy:y0{hr}=h{hr} by smt().
                             by rewrite hx hy.
                           + rcondt{2} 1.
                             + move=> &m; auto; move=> &hr hs.
                               have hxx:x{hr}=c{hr} by smt().
                               have hyy:y0{hr}=h{hr} by smt().
                               have hcc:c{hr}=c{m} by smt().
                               have hhh:h{hr}=h{m} by smt().
                               have hx:x{hr}=c{m} by rewrite hxx hcc.
                               have hy:y0{hr}=h{m} by rewrite hyy hhh.
                               have hn:!has (fun (u:pdh option*pdh*pdh) _=>u.`2=c{m} /\ u.`3=h{m}) Game4_b.h_map{m} by smt().
                               have hf:=red_pair_fresh Game4_b.h_map{m} c{m} h{m} hn None.
                               have hc:red_cache Exp_b.c_map{m} Exp_b.ich{m} St_CDH.y_map{hr} Game4_b.h_map{m} B2.h_map{hr} by smt().
                               have hm:(None,c{m},h{m}) \notin B2.h_map{hr} by rewrite /red_cache in hc; smt().
                               by rewrite hx hy.
                             + outline {1} [1 .. 4] by { k <@ FinalResponseKeys.random(c,h); }.
                               outline {2} [1 .. 3] by { k <@ FinalResponseKeys.real(c,h); }.
                               exists* Exp_b.c_map{1}; elim*=> cm0.
                               move=> rmR rmL.
                               exists* Exp_b.ich{1}; elim*=> ich0.
                               exists* St_CDH.y_map{2}; elim*=> ym1.
                               exists* i{1}; elim*=> i0.
                               exists* c{1}; elim*=> c0.
                               exists* h{1}; elim*=> h0.
                               wp; call (final_response_key_readback cm0 (ich0 `|` fset1 i0) ym1 c0 h0).
                               auto; move=> &1 &2 hs.
                               have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
                                Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
                                B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
                                St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
                               have hf:find (fun v _=>Exp_b.p_map{1}.[v]=Some j{1} /\ Exp_b.i_map{1}.[v]=Some c{1})
                                Exp_b.c_map{1}=Some i{1} by smt().
                               have hxp:i{1} \notin Exp_b.xp{1} by smt().
                               have hy:St_CDH.y_map{2}.[St_CDH.m{2}]=Some y{1} by smt().
                               have hp:=red_shape_response_challenge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                j{1} c{1} i{1} St_CDH.m{2} y{1} hshape hf hxp hy.
                               have hc:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
                                Game4_b.h_map{1} B2.h_map{2} by smt().
                               have hh:=red_cache_challenge Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
                                Game4_b.h_map{1} B2.h_map{2} i{1} hc.
                               smt().

                       + rcondf{1} 3.
                         + move=> &m; wp; call (:true); auto=> />; smt().
                         + swap{1} 2 -1; swap{2} 2 -1; sp 1 1.
                               exists* Exp_b.c_map{1}; elim*=> cm0.
                               move=> rmR rmL.
                               exists* Exp_b.ich{1}; elim*=> ich0.
                               exists* St_CDH.y_map{2}; elim*=> ym1.
                               exists* i{1}; elim*=> i0.
                               exists* c{1}; elim*=> c0.
                               exists* h{1}; elim*=> h0.
                               wp; call (final_hprime_cache cm0 (ich0 `|` fset1 i0) ym1 c0 h0 true).
                               auto; move=> &1 &2 hs.
                               have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
                                Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
                                B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
                                St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
                               have hf:find (fun v _=>Exp_b.p_map{1}.[v]=Some j{1} /\ Exp_b.i_map{1}.[v]=Some c{1})
                                Exp_b.c_map{1}=Some i{1} by smt().
                               have hxp:i{1} \notin Exp_b.xp{1} by smt().
                               have hy:St_CDH.y_map{2}.[St_CDH.m{2}]=Some y{1} by smt().
                               have hp:=red_shape_response_challenge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                j{1} c{1} i{1} St_CDH.m{2} y{1} hshape hf hxp hy.
                               have hc:red_cache Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
                                Game4_b.h_map{1} B2.h_map{2} by smt().
                               have hh:=red_cache_challenge Exp_b.c_map{1} Exp_b.ich{1} St_CDH.y_map{2}
                                Game4_b.h_map{1} B2.h_map{2} i{1} hc.
                               have hn:!has (fun (u:pdh option*pdh*pdh) _=>u.`2=c{1} /\ u.`3=h{1}) Game4_b.h_map{1} by smt().
                               have hfr:=red_pair_fresh Game4_b.h_map{1} c{1} h{1} hn None.
                               smt().
                 + rcondf{1} 3.
                   + move=> &m; wp; call (:true); auto=> />; smt().
                   + rcondf{2} 3.
                     + move=> &m; wp; call (:true); auto=> />; smt().
                     + swap{1} 2 -1; swap{2} 2 -1; sp 1 1.
                       exists* Exp_b.c_map{1}; elim*=> cm0.
                       move=> rmR rmL.
                       exists* Exp_b.ich{1}; elim*=> ich0.
                       exists* St_CDH.y_map{2}; elim*=> ym1.
                       exists* c{1}; elim*=> c0.
                       exists* h{1}; elim*=> h0.
                       wp; call (final_hprime_cache cm0 ich0 ym1 c0 h0 true).
                       auto; move=> &1 &2 hs.
                       have hn:!has (fun (u:pdh option*pdh*pdh) _=>u.`2=c{1} /\ u.`3=h{1}) Game4_b.h_map{1} by smt().
                       have hfr:=red_pair_fresh Game4_b.h_map{1} c{1} h{1} hn None.
                       smt().

         + swap{1} 2 -1; swap{2} 2 -1.
           seq 1 1:(red_inv bit (glob S){1} (glob S){2}
            (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
            B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
            Game4_b.h_map{1} B2.h_map{2} /\ !St_CDH.win{2} /\ ={j,c,ch,h,sig,c'} /\
            io{1}=None /\ io{2}=None /\ y{2}=y{1}).
           + auto; move=> &1 &2 hs.
             have hshape:red_shape Exp_b.n{1} Exp_b.m{1} St_CDH.n{2} St_CDH.m{2}
              Exp_b.c_map{1} Exp_b.p_map{1} Exp_b.i_map{1} Exp_b.pk_map{1}
              B2.x_idx{2} St_CDH.x_map{2} St_CDH.y_map{2} Exp_b.xp{1} Exp_b.ich{1}
              St_CDH.cr_1{2} St_CDH.cr_2{2} by smt().
             have he:=red_shape_response_find _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              j{1} c{1} hshape.
             have hn:!has (fun a jj=>jj=j{1} /\ Exp_b.i_map{1}.[a]=Some c{1}) Exp_b.p_map{1} by smt().
             have hf:=final_no_has_find _ _ hn.
             have hpm:Exp_b.p_map{2}=Exp_b.p_map{1} by smt().
             have him:Exp_b.i_map{2}=Exp_b.i_map{1} by smt().
             have hj:j{2}=j{1} by smt().
             have hcc:c{2}=c{1} by smt().
             have hmsg:c'{1}=c'{2} by move: hs=> />.
             rewrite hpm him hj hcc /= he hf; smt().
           + match None{1} 2.
             + by move=> &m; wp; call (:true); auto=> />.
             + match None{2} 2.
               + by move=> &m; wp; call (:true); auto=> />.
               + wp; call (final_h_state bit); auto=> />; smt().
 + by auto=> />.
qed.

local lemma cdh_gen1_keeps_win:hoare[CDHR.Oracles.gen_1:St_CDH.win ==> St_CDH.win].
proof. by proc; auto=> />; smt(). qed.

local lemma cdh_gen2_keeps_win:hoare[CDHR.Oracles.gen_2:St_CDH.win ==> St_CDH.win].
proof. by proc; auto=> />; smt(). qed.

local lemma cdh_corrupt1_keeps_win:hoare[CDHR.Oracles.corrupt_1:St_CDH.win ==> St_CDH.win].
proof. by proc; auto=> />; smt(). qed.

local lemma b2_hprime_keeps_win:hoare[SimR.Oracles.h':St_CDH.win ==> St_CDH.win].
proof.
 proc; if; auto.
qed.

local lemma b2_h_keeps_win:hoare[SimR.Oracles.h:St_CDH.win ==> St_CDH.win].
proof.
 proc; sp; if.
 + seq 1:St_CDH.win; first by call cdh_ddh_keeps_win; auto.
   if; first by wp; call b2_hprime_keeps_win; auto.
   by auto.
 + by auto.
qed.



local lemma final_adversary_coupling bit:
 equiv[A(Game4_b.Oracles).distinguish ~ A(SimR.Oracles).distinguish:
 ={glob A} /\ !St_CDH.win{2} /\ red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2}
 ==> !St_CDH.win{2} => red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2} /\ ={glob A,res}].
proof.
 proc *; call (_: St_CDH.win,red_inv bit (glob S){1} (glob S){2}
  (glob Exp_b){1} (glob Exp_b){2} (glob St_CDH){2}
  B2.n_x{2} B2.x_idx{2} Game2_b.resp_inputs{1} B2.resp_inputs{2}
  Game4_b.h_map{1} B2.h_map{2},true).
 + exact A_ll.
 + by conseq (final_gen_state bit)=> //; smt().
 + move=> &m _; proc; islossless; exact S_keygen_ll.
 + move=> &m; conseq b2_gen_ll (_: St_CDH.win ==> St_CDH.win)=> //.
   by proc; wp; call (:true); auto=> />; smt().
 + by conseq (final_corrupt_state bit)=> //; smt().
 + move=> &m _; by proc; auto=> />; smt().
 + move=> &m; conseq b2_corrupt_ll (_: St_CDH.win ==> St_CDH.win)=> //.
   by proc; auto=> />; smt().
 + by conseq (final_expose_state bit)=> //; smt().
 + move=> &m _; by proc; auto=> />; smt().
 + move=> &m; conseq b2_expose_ll (_: St_CDH.win ==> St_CDH.win)=> //.
   proc; sp; if; last by auto.
   sp; if; last by auto.
   by wp; call cdh_corrupt1_keeps_win; auto.
 + by conseq (final_init_state bit)=> //; smt().
 + move=> &m _; proc; islossless; do ?(match; islossless).
 + move=> &m; conseq b2_init_ll (_: St_CDH.win ==> St_CDH.win)=> //.
   proc; seq 2:St_CDH.win; first by call cdh_gen1_keeps_win; auto.
   by auto=> /> /#.
 + by conseq (final_respond_state bit)=> //; smt().
 + move=> &m _; proc; inline *; islossless; try exact S_sign_ll; do ?(match; islossless).
 + move=> &m; conseq b2_respond_ll (_: St_CDH.win ==> St_CDH.win)=> //.
   proc; sp; if; last by auto.
   sp; seq 1:St_CDH.win.
   + if; first by call cdh_gen2_keeps_win; auto.
     by auto.
   + if; first by auto.
     seq 2:St_CDH.win; first by call (:true); auto.
     sp; seq 1:St_CDH.win.
     + if; first by call b2_hprime_keeps_win; auto.
       by call b2_h_keeps_win; auto.
     + sp; match; auto.
 + by conseq (final_receive_state bit)=> //; smt().
 + move=> &m _; proc; inline Game4_b.Oracles.h'; islossless.
 + move=> &m; conseq b2_receive_ll (_: St_CDH.win ==> St_CDH.win)=> //.
   proc; sp; if; last by auto.
   sp; if; last by auto.
   sp 1; seq 1:St_CDH.win; first by auto.
   seq 1:St_CDH.win.
   + if; first by wp; call b2_hprime_keeps_win; auto.
     by auto.
   + by auto.
 + by conseq (final_h_state bit)=> //; smt().
 + move=> &m _; proc; inline *; islossless; do ?(match; islossless).
 + by move=> &m; conseq b2_h_ll b2_h_keeps_win=> //.
 + by auto=> />; smt().
qed.

local lemma final_run_coupling bit:
 equiv[Game4_b.run ~ ReductionTrace.run:
 ={glob A,glob S} /\ b{1}=bit ==> !St_CDH.win{2} => ={res}].
proof.
 proc; call (final_adversary_coupling bit); inline RO.init.
 auto=> />; rewrite /red_erase FMap.map_empty /red_shape /red_cache /red_protected.
 smt(FMap.emptyE FMap.mem_empty in_fset0).
qed.


(* Lemma for final reduction *)

local lemma Reduction &m:
  `|Pr[Game4_b.run(false) @ &m: res] - Pr[Game4_b.run(true) @ &m: res]|
  <= Pr[St_CDH(B2(S,A)).run() @ &m: res].

(* Proof by GPT-6.1-Sol *)

proof.
 have hg:forall bit (event:bool -> bool),
  Pr[ReductionTrace.run()@&m:!St_CDH.win /\ event res] <=
  Pr[Game4_b.run(bit)@&m:event res].
 + move=> bit event.
   byequiv (: ={glob A,glob S} /\ b{2}=bit ==> !St_CDH.win{1} => ={res})=> //.
   + symmetry; conseq (final_run_coupling bit)=> //; smt().
   + smt().
 have hs:
  Pr[ReductionTrace.run()@&m:!St_CDH.win /\ res]+
  Pr[ReductionTrace.run()@&m:!St_CDH.win /\ !res] =
  1%r-Pr[ReductionTrace.run()@&m:St_CDH.win].
 + have hgood:Pr[ReductionTrace.run()@&m:!St_CDH.win] =
    1%r-Pr[ReductionTrace.run()@&m:St_CDH.win].
   + rewrite Pr[mu_not] (:Pr[ReductionTrace.run()@&m:true]=1%r); first by byphoare trace_ll=> //.
     by trivial.
   by rewrite -hgood eq_sym Pr[mu_split res].
 have hp:forall bit,
  Pr[Game4_b.run(bit)@&m:res]+Pr[Game4_b.run(bit)@&m:!res] <= 1%r.
 + by move=> bit; rewrite Pr[mu_not] RField.addrC RField.subrK Pr[mu_le1].
 have hrt:=hg false (fun r=>r); have hrf:=hg false (fun r=>!r).
 have hit:=hg true (fun r=>r); have hif:=hg true (fun r=>!r).
 have h0:=hp false; have h1:=hp true; have hw:=trace_win_equiv &m.
 smt().
qed.



(* Putting everything together *)

local lemma Security_of_SignedDH &m:
  (forall b, Pr[Game2_b.run(b) @ &m: Game2_b.bad_2] <= p_2) =>
  (forall b, Pr[Game4_b.run(b) @ &m: Game4_b.bad_4] <= p_4) =>
  `|  Pr[Exp_b(SignedDH(S), RO, A).run(false) @ &m : res]
    - Pr[Exp_b(SignedDH(S), RO, A).run(true) @ &m : res]|
  <=   Pr[SUFCMA(S, B1_0(S, A)).run() @ &m: res]
     + Pr[SUFCMA(S, B1_1(S, A)).run() @ &m: res]
     + Pr[St_CDH(B2(S,A)).run() @ &m: res]
     + Pr[Game1_b.run(true) @ &m: Game1_b.bad_1]
     + Pr[Game1_b.run(false) @ &m: Game1_b.bad_1]
     + 2%r * p_2
     + 2%r * p_4.
proof.
move=> hp2 hp4.
have h0:=Hop0 &m.
have h10:=Hop1 false &m; have h11:=Hop1 true &m.
have hx0:=Bad2 false &m (hp2 false); have hx1:=Bad2 true &m (hp2 true).
have h20:=Hop3 false &m; have h21:=Hop3 true &m.
have hs0:=Reduction1_0 &m; have hs1:=Reduction1_1 &m.
have h30:=Bad4 false &m (hp4 false); have h31:=Bad4 true &m (hp4 true).
have hcdh:=Reduction &m.
smt().
qed.
end section.
