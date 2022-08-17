MaximalOrder:=function(G)
  if IsAbelian(G) then
     B := AbelianBasis(G);
     return B[#B];
  end if;
  C := ConjugacyClasses(G);
  m, i := Max([x[1] : x in C]);
  return C[i][3];
end function;


CentralProduct:=function(n,H,Z)
  T:=H meet Z;
  k1:=Order(T);
  if Order(Z) eq 1 then
     return H;
  end if;
  p:=Order(H);
  k2:=n*k1;
  k:=k2 div p;
  C:=CyclicGroup(k);
  B, inc:=DirectProduct(H, C);
  x:=MaximalOrder(Z);
  y:=MaximalOrder(C);
  z:=Order(Z);
  a:=z div k1;
  b:=k div k1;
  N:=sub<B|inc[1](x^a)*inc[2](y^b)>;
  return B / N;
end function;


PermGroup2:=function(G)
  S:=Subgroups(G);
  n:=#S;
  for i in [n..1 by -1] do
      H:=S[i]`subgroup;
      rho, GH, K:=CosetAction(G,H);
      if Order(K) eq 1 then
         if IsIsomorphic(G, GH) then
            return GH, i;
         end if;
      end if;
  end for;
end function;


CentralExtensionsIsMinimalLift:=function(G)

  Z:=Center(G);
  n:=Order(G);
  S:=Subgroups(G : OrderMultipleOf:=#G div Exponent(G));
  k:=#S;
  k:=k-1;
  for j in [k..1 by -1] do
      H:=S[j]`subgroup;
      C:=CentralProduct(n, H, Z);
      if Order(MaximalOrder(C)) eq Order(MaximalOrder(G)) and Exponent(C) eq Exponent(G) then
         if IsIsomorphic(C, G) then
            return false;
         end if;
      end if;
  end for;
  return true;
end function;


TrivialActionConstruction:=function(G)
  n:=Ngens(G);
  x:=[];
  for i in [1..n] do
      x[i]:=[1];
  end for;
  return x;
end function;


PermGroup:=function(G)
  H:=sub<G|Id(G)>;
  T:=CosetTable(G,H);
  return CosetTableToPermutationGroup(G,T);
end function;

FaithfulRepresentationOfFixedDegree:=function(G, k)
  T:=CharacterTable(G);
  n:=#T;
  X:=[];
  c:=1;
  i:=1;
  while T[i][1] le k do
	if T[i][1] eq k and IsFaithful(T[i]) then
	   return true;
        end if;
        i:=i+1;
  end while;
  return false;
end function;

PossibleLiftsOfFixedLength:=function(G, n, k)
  if n eq 1 then
     if FaithfulRepresentationOfFixedDegree(G, k) then
        if CentralExtensionsIsMinimalLift(G) then
           return [G];
        end if;
     end if;
     retrun [];
  end if;
  x:=TrivialActionConstruction(G);
  M:=CohomologyModule(G, [n], x);
  D:=DistinctExtensions(M);
  m:=#D;
  y:=[];
  c:=0;
  for i in [1..m] do
      H:=PermGroup(D[i]);
      if FaithfulRepresentationOfFixedDegree(H, k) then
         if CentralExtensionsIsMinimalLift(H) then
            c:=c+1;
            y[c]:=H;
         end if;
      end if;
  end for;
  return y;
end function;


IdentificationForSmallGroups:=function(G,n)
  H:=PossibleLiftsOfFixedLength(G,n);
  n:=#PossibleLiftsOfFixedLength(G,n);
  if n eq 0 then
     return 0;
  end if;
  for i in [1..n] do
      print IdentifyGroup(H[i]);
  end for;
  return 0;
end function;



MinimalLiftsOfFixedLengthAndFixedDimension:=function(G, n, k)
  x:=PossibleLiftsOfFixedLength(G, n);
  l:=#x;
  y:=[];
  c:=1;
  for i in [1..l] do
      H:=x[i];
      if FaithfulRepresentationOfFixedDegree(H, k) then
         y[c]:=H;
         c:=c+1;
      end if;
  end for;
  return y;
end function;


SpecialIndex:=function(a, b)
  G:=SmallGroup(a,b);
  H:=CommutatorSubgroup(G,G,G);
  Z:=Center(G);
  return Index(H, Z);
end function;


GroupHomology:=function(G, n)
  if n eq 1 then
     H:=AbelianQuotient(G);
     return PermGroup2(PCGroup(H));
  end if;
  if n eq 2 then
     if IsSolvable(G) then
        G:=PermGroup2(G);
     end if;
     n:=Order(G);
     x:=PrimeDivisors(n);
     m:=#x;
     y:=CyclicGroup(pMultiplicator(G, x[1])[1]);
     for i in [2..m] do
         y:=DirectProduct(y, CyclicGroup(pMultiplicator(G, x[i])[1]));
     end for;
     return y;
  end if;
end function;


PossibleOrders:=function(G)
  H1:=GroupHomology(G,1);
  H2:=GroupHomology(G,2);
  H:=DirectProduct(H1,H2);
  n:=Exponent(H);
  return Divisors(n);
end function;


MinimalLifts:=function(n)
  if n eq 2 then
     x:=<Group("A4"), Group("S4"), Group("A5")>;
     a:=#x;
     for i in [1..a] do
         c:=PossibleOrders(x[i]);
         for j in c do
 	     print PossibleLiftsOfFixedLength(PermGroup2(x[i]), j, n);
         end for;
     end for;
  end if;
  if n eq 3 then
     y:=<SmallGroup(36,9), SmallGroup(72,41), SmallGroup(216,153), Group("A5"), Group("A6"), Group("PSL(2,7)")>;
     b:=#y;
     for i in [1..b] do
         c:=PossibleOrders(y[i]);
         for j in c do
	     print PossibleLiftsOfFixedLength(PermGroup2(y[i]), j, n);
         end for;
     end for;
  end if;
  return 0;
end function;


MinimalLiftComputation:=function(G, n)
  G:=PermGroup2(G);
  c:=PossibleOrders(G);
  x:=[];
  for i in c do
      x[i]:=PossibleLiftsOfFixedLength(G, i, n);
  end for;
  return x;
end function;


PrimitiveCharacter:=function(c, G)

  S:=Subgroups(G : OrderMultipleOf:=Numerator(Order(G)) div Numerator(c[1]));
  n:=Order(G);
  k:=#S;
  k:=k-1;
  for i in [1..k] do
      H:=S[i]`subgroup;
      m:=Order(H);
      p:=m*Numerator(c[1]);
      q:=p div n;
      C:=CharacterTable(H);
      X:=[Induction(x, G): x in C| x[1] eq q];
      if c in X then
         return false;
      end if;
  end for;
  return true;
end function;

Primi:=function(G)

  G:=PermGroup2(G);
  B:=CharacterTable(G);
  X:=[x:x in B|IsFaithful(x)];
  for x in X do
      if PrimitiveCharacter(x, G) then
	  return true;
      end if;
  end for;
  return false;
end function;

CategoryI:=function(G, H)
  G:=PermGroup2(G);
  H:=PermGroup2(H);
  A:=Center(G);
  B:=Center(H);
  D, inc:=DirectProduct(G, H);
  return D / sub<D|inc[1](A.1)*inc[2](B.1)>;
end function;

DP:=function(G, H)
  G:=PermGroup2(G);
  H:=PermGroup2(H);
  return DirectProduct(G, H);
end function;

SDH := function(p)
  E := ExtraSpecialGroup(p,1);
  H, phi := Holomorph(E);
  N := phi(E);  //the image of E in H
  D := DerivedGroup(H);  //to get SL on top
  P := pCore(D,p);
  C := Complements(D,P);
  return sub< D | N, C[1] >;
end function;

These are our functions!

