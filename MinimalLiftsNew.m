MaximalOrder:=function(G)

  '''this function is used to find an element of Order(G) inside the group G by successively
     multiplying Generators of G until the obtained element has the desired order.'''
  x:=[z:z in Generators(G)];
  a:=x[1]; 
  n:=Order(G);
  i:=1;
  while Order(a) ne n do
	i:=i+1;
        a:=a*x[i];
  end while;
  return a;
end function;


CentralProductPC:=function(n,H,Z)

  '''this function is used to compute the Central Product of H, a subgroup of an order n group G
  with center Z, and a cyclic group of order k with respect to the cyclic group of order k1, where
  k1 is the order of the intersection of H and Z and k is equal to n*k1/Order(H). This function is
     specifically used for Polycyclic Groups.'''

  T:=H meet Z;
  k1:=Order(T);
  if Order(Z) eq 1 then
     return H;
  end if;
  p:=Order(H);
  k2:=n*k1;
  k:=k2/p;
  k:=Numerator(k);
  C:=PCGroup(CyclicGroup(k));
  B, inc:=DirectProduct(H, C);
  x:=MaximalOrder(Z);
  y:=MaximalOrder(C);
  z:=Order(Z);
  a:=z/k1;
  a:=Numerator(a);
  b:=k/k1;
  b:=Numerator(b);
  N:=sub<B|inc[1](x^a)*inc[2](y^b)>;
  return B / N;
end function;


CentralProductPerm:=function(n,H,Z)

  '''this function is used to compute the Central Product of H, a subgroup of an order n group G
  with center Z, and a cyclic group of order k with respect to the cyclic group of order k1, where
  k1 is the order of the intersection of H and Z and k is equal to n*k1/Order(H). This function is
     specifically used for Permutation Groups.'''

  T:=H meet Z;
  k1:=Order(T);
  if Order(Z) eq 1 then
     return H;
  end if;
  p:=Order(H);
  k2:=n*k1;
  k:=k2/p;
  k:=Numerator(k);
  C:=CyclicGroup(k);
  B, inc:=DirectProduct(H, C);
  x:=MaximalOrder(Z);
  y:=MaximalOrder(C);
  z:=Order(Z);
  a:=z/k1;
  a:=Numerator(a);
  b:=k/k1;
  b:=Numerator(b);
  N:=sub<B|inc[1](x^a)*inc[2](y^b)>;
  return B / N;
end function;


CentralExtensionIsMinimalLift:=function(G)

  '''this function is used to check if a Central Extension is in fact a minimal lift, which is equivalent to checking
  if G is isomorphic to any of the Groups given by CentralProductPC(n, H, Z), where H runs through the subgroups of G
  n is the order of G and Z is the center of G, in case G is a policyclic group, or isomorphic to any of the Groups
  given by CentralProductPerm(n, H, Z), where H, Z and n are defined in the same way, in case G is not solvable. This
     distinction is made because of the different isomorphism functions for soluble and non-soluble groups given by
  magma. Then, the function returns 'false' if G is indeed isomorphic to any of those groups, and 'true' if it
  isn't. Note that this does not fully check the Minimal Lift property, since we still have to check if these have
  faithful irreducible representations of a given degree, which we come later.'''

  Z:=Center(G);
  n:=Order(G);
  S:=Subgroups(G);
  k:=#S;
  k:=k-1;
  if IsSolvable(G) then
     for j in [k..1 by -1] do
         H:=S[j]`subgroup;
         if IsIsomorphicSolubleGroup(CentralProductPC(n, H, Z), G) then
            return false;
         end if;
     end for;
   else
     for j in [k..1 by -1] do
	 H:=S[j]`subgroup;
         if IsIsomorphic(CentralProductPerm(n, H, Z), G) then
            return false;
         end if;
     end for;
   end if;
   return true;
end function;


TrivialActionConstruction:=function(G)

  '''this function is used to build the trivial action of a group G (a.k.a., a set of Ngens(G) [1]'s) which will later
     be used to find the cohomology modules used in the construction of central extensions'''

  n:=Ngens(G);
  x:=[];
  for i in [1..n] do
      x[i]:=[1];
  end for;
  return x;
end function;


PermGroup2:=function(G)

  '''this function describes one method of finding a permutation representation of a group G. However, this function
  does not work for Finitely Presented Group Representations, since the Subgroups function cannot take such a
  representation as an argument. Then, we must define another, possibly less efficient, way of finding a permutation
  representation, at least for the time being.'''

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


PermGroup:=function(G)

  '''this function describes another method of finding a permutation representation of a group G. Unlike PermGroup2,
  this function does not work for PolyCyclic groups, but will convert finitely presented groups to permutation
  groups and so solves the problem found in PermGroup2. Then, we shall use these two functions alternatively
     when one proves to be more useful than the other.'''

  H:=sub<G|Id(G)>;
  T:=CosetTable(G,H);
  return CosetTableToPermutationGroup(G,T);
end function;


PossibleLiftsOfFixedOrder:=function(G, n)

  '''this function constructs the possible lifts of a fixed order. Basically, we construct the central extensions of G
  by the Cyclic Group of order n, which are given by the trivial action of G using the function
  TrivialActionConstruction, and then check if they could be Minimal Lifts (again, we will check the existence of
									    faithful irreducible representations later). Then, we distinguish two possible cases, as usual: if G is solvable,
						      and if it isn't. Then, in the case that it is solvable, we will return the possible lifts as policyclic groups,
						      and if it is non-solvable, we will return the possible lifts as permutation groups. Note that we must use the
						      PermGroup function, and not the PermGroup2 function, since the central extensions are given as FPGroups. To build
						      the central extensions, we build the cohomology module and the second cohomology group given by this moduel,
						      and the using the DistinctExtensions function to find these extensions. Then, we return a list of the possible
						         extensions.'''

  y:=[];
  c:=0;
  if n eq 1 then
     if CentralExtensionsIsMinimalLift(G) then
        y[1]:=G;
        c:=1;
     end if;
     return y;
  end if;
  x:=TrivialActionConstruction(G);
  M:=CohomologyModule(G, [n], x);
  P:=CohomologyGroup(M, 2);
  D:=DistinctExtensions(M);
  m:=#D;
  if IsSolvable(G) then
     for i in [1..m] do
         H:=PCGroup(D[i]);
         if CentralExtensionsIsMinimalLift(H) then
            c:=c+1;
            y[c]:=H;
         end if;
     end for;
   else
     for i in [1..m] do
	 H:=PermGroup(D[i]);
         if CentralExtensionsIsMinimalLift(H) then
            c:=c+1;
            y[c]:=H;
         end if;
     end for;
  end if;
  return y;
end function;


IdentificationForSmallGroups:=function(G,n)

  '''Not really needed. This function is used to return the ID's of groups found by running the previous function in
     order to check if they are indeed the groups found by Kimball Martin.'''

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


FaithfulRepresentationOfFixedDegree:=function(G, k)

  '''This function is used to check if the group G has a faithful irreducible degree k representation. To do this, we
													       generate the Character Table of G, find if there exists an irreducible representation of degree k, and then
  check if there exists another character of that representation equal to k. If such a character exists, then
  the representation is not faithful, and if it doesn't, then the representation is faithful. Thus, if we don't
  end up finding such a representation, return false, and if we do, return true.'''

								      n:=Nclasses(G);
  T:=CharacterTable(G);
  i:=2;
  while T[i][1] le k and i le n do
	if T[i][1] eq k then
	   j:=2;
           while j le n and T[i][j] ne k do
	         j:=j+1;
           end while;
           if j eq n+1 then
              return true;
           end if;
         end if;
         i:=i+1;
  end while;
  return false;
end function;


MinimalLiftsOfFixedOrderAndFixedDimension:=function(G, n, k)

  '''This function is basically a combination of the past few functions in order to check if the Possible Minimal Lifts
  to GL(k,C) are actually minimal lifts by looking at the representations of G and finiding if there exists a
  faithful degree k representation. Thus, we take the PossibleLiftsOfFixedLength(G,n), run through the possible lifts
    found, and store those which have faithful irreducible degree k representations. Then, return the lifts which have
    these properties, since these are the minimal lifts we have been looking for.'''

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

  '''This function is related to the Feit paper. For G:=SmallGroup(a,b), return the index of the Commutator Subgroup
  and the Center of G. This only works if the center is contained inside the commutator, which is a property of
  the subgroups given by Feit. A bit out of place here, but sort of useful.'''

  G:=SmallGroup(a,b);
  H:=CommutatorSubgroup(G,G,G);
  Z:=Center(G);
  return Index(H, Z);
end function;


GroupHomology:=function(G, n)

  '''This function is used to compute the first and second Group Homologies of group G, which are given by calling the
  function for (G, 1) or (G, 2). To compute H_1(G, Z), we only compute the AbelianQuotient of our group and return
			its Permutation Representation (in order to quickly compute the direct product of H1 and H2 later). Then, to
			compute H_2(G, Z), we take H, the permutation representation of group G, and its order n, and compute the direct
			product of the cyclic groups given by the p-part of the Schur Multiplier of H, where p runs through the distinct
			prime factor of G. Then, just return the group obtained, since this is the second homology group of G.'''

  if n eq 1 then
     H:=AbelianQuotient(G);
     return PermGroup2(PCGroup(H));
  end if;
  if n eq 2 then
     H:=PermGroup2(G);
     n:=Order(H);
     x:=PrimeDivisors(n);
     m:=#x;
     y:=CyclicGroup(pMultiplicator(H, x[1])[1]);
     for i in [2..m] do
         y:=DirectProduct(y, CyclicGroup(pMultiplicator(H, x[i])[1]));
     end for;
     return y;
  end if;
end function;


PossibleOrders:=function(G)

  '''Using the Theorem in Kimball Martin's paper, we know that minimal lifts are just central extensions by Cyclic
  Groups of order m, where m is a divisor of the exponent of H_1(G,Z)XH_2(G,Z). Then, just let H1:=GroupHomology(G,1)
  and H2:=GroupHomology(G,2), and then take n:=Exponent(H) and return Divisors(n).'''

  H1:=GroupHomology(G,1);
  H2:=GroupHomology(G,2);
  H:=DirectProduct(H1,H2);
  n:=Exponent(H);
  return Divisors(n);
end function;


MinimalLifts:=function(n)

  '''This function currently works for n=2,3. Knowing the finite subgroups of PGL(n,C), we compute the minimal lifts
  by finding the possible extensions using the PossibleOrders function, and then returning the
  MinimalLiftsOfFixedLengthAndFixedDimension by running through the orders found previously. Then, this function
     returns all possible minimal lifts of finite subgroups of the projective linear group. Will expand for higher
     dimensions.'''

  if n eq 2 then
     x:=<Group("A4"), Group("S4"), Group("A5")>;
     a:=#x;
     for i in [1..a] do
         c:=PossibleOrders(x[i]);
         for j in c do
	     print MinimalLiftsOfFixedLengthAndFixedDimension(x[i], j, n);
         end for;
     end for;
  end if;
  if n eq 3 then
     y:=<SmallGroup(36,9), SmallGroup(72,41), SmallGroup(216,153), Group("A5"), Group("A6"), Group("PSL(2,7)")>;
     b:=#y;
     for i in [1..b] do
         c:=PossibleOrders(y[i]);
         for j in c do
	     print MinimalLiftsOfFixedLengthAndFixedDimension(y[i], j, n);
         end for;
     end for;
  end if;
  return 0;
end function;

