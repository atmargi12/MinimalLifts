MaximalOrder:=function(G)
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


CentralExtensionsIsMinimalLift:=function(G)
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


PossibleLiftsOfFixedLength:=function(G, n)
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


MinimalLifts:=function(n)
  if n eq 2 then
  print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A4"), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A4"), 2, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A4"), 3, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A4"), 6, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("S4"), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("S4"), 2, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A5"), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A5"), 2, n);
end if;

if n eq 3 then
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(36,9), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(36,9), 2, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(36,9), 3, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(36,9), 4, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(36,9), 6, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(36,9), 12, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(72,41), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(72,41), 2, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(72,41), 3, n);print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(72,41), 6, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(216,153), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(SmallGroup(216,153), 3, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A5"), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A5"), 2, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A6"), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A6"), 2, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A6"), 3, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("A6"), 6, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("PSL(2,7)"), 1, n);
print MinimalLiftsOfFixedLengthAndFixedDimension(Group("PSL(2,7)"), 2, n);
end if;
return 0;
end function;


SpecialIndex:=function(a, b)
  G:=SmallGroup(a,b);
H:=CommutatorSubgroup(G,G,G);
Z:=Center(G);
return Index(H, Z);
end function;
