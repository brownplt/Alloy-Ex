//Signatures
sig Data { }
sig Secrets { }
sig userName { }
sig repoName { }
sig User {
name: one userName,
info: set Data,
action: set Actions,
secret: lone Secrets }
sig Repo {
name: one repoName,
owner: one userName,
readUsers: some userName,
writeUsers: some readUsers,
contents: set Data }
sig State{
repos: set Repo,
users: set User}
sig Actions{ }
one sig CreateRepo in Actions { }
one sig DeleteRepo in Actions { }
one sig Push in Actions { }
one sig Pull in Actions { }
one sig GrantRead in Actions { }
one sig RevokeRead in Actions { }
one sig GrantWrite in Actions { }
one sig RevokeWrite in Actions { }
one sig CreateAccount in Actions { }
one sig DeleteAccount in Actions { }

//Predicates
pred CreatingRepo [u:User, r:Repo, s,s':State] {
	u.action=CreateRepo && r !in s.repos && r in s'.repos && u in s.users && u in s'.users
	&& s.users=s'.users && s.repos+r=s'.repos}
pred DeletingRepo [u:User, r:Repo, s,s':State] {
	u.action=DeleteRepo && r in s.repos && r !in s'.repos && u in s.users && u in s'.users
	&& s.users=s'.users && s.repos-r=s'.repos}
pred GrantingRead [u,u':User, r,r':Repo, s,s':State] {
	r.owner=u.name && u.action=GrantRead && u'.name !in r.readUsers 
	&& u'.name in r'.readUsers && r in s.repos && r' in s'.repos && r.name=r'.name
	u in s.users && u in s'.users && u' in s.users && u' in s'.users
	&& s.users=s'.users && s.repos-r+r'=s'.repos}
pred RevokingRead [u,u':User, r,r':Repo, s,s':State] {
	r.owner=u.name && u.action=RevokeRead && u'.name in r.readUsers && 
	u'.name !in r'.readUsers && r in s.repos && r' in s'.repos && r.name=r'.name
	u in s.users && u in s'.users && u' in s.users && u' in s'.users
	&& s.users=s'.users && s.repos-r+r'=s'.repos}
pred GrantingWrite [u,u':User, r,r':Repo, s,s':State] {
	r.owner=u.name && u.action=GrantWrite && u'.name !in r.writeUsers 
	&& u'.name in r'.writeUsers && r in s.repos && r' in s'.repos && r.name=r'.name
	u in s.users && u in s'.users && u' in s.users && u' in s'.users
	&& s.users=s'.users && s.repos-r+r'=s'.repos}
pred RevokingWrite [u,u':User, r,r':Repo, s,s':State] {
	r.owner=u.name && u.action=RevokeWrite && u'.name in r.writeUsers && 
	u'.name !in r'.writeUsers && r in s.repos && r' in s'.repos && r.name=r'.name
	u in s.users && u in s'.users && u' in s.users && u' in s'.users
	&& s.users=s'.users && s.repos-r+r'=s'.repos}
pred CreatingAccount [u,u':User, c:Secrets, s,s':State] {
	u in s.users && u' in s'.users && u.name=u'.name &&
	u.action=CreateAccount && u.secret=none && u'.secret=c
	&& s.users-u+u'=s'.users && s.repos=s'.repos}
pred DeletingAccount [u,u':User, c:Secrets, s,s':State] {
	u in s.users && u' in s'.users && u.name=u'.name &&
	u.action=DeleteAccount && u.secret=c && u'.secret=none
	&& s.users-u+u'=s'.users && s.repos=s'.repos}
pred Pushing [u:User, r,r':Repo, d:Data, s,s':State] {
	u.name in r.writeUsers && d in u.info && d !in r.contents && u.action=Push && d in r'.contents 
	&& r in s.repos && r' in s'.repos && u in s.users && r.name=r'.name
	&& s.users=s'.users && s.repos-r+r'=s'.repos}
pred Pulling [u,u':User, r:Repo, d:Data, s,s':State] {
	u.name in r.writeUsers && d !in u.info && d in r.contents && u.action=Pull
	&& d in u'.info && r in s.repos && u in s.users && u' in s'.users && u.name=u'.name
	&& s.users-u+u'=s'.users && s.repos=s'.repos}
pred Transition [s,s':State] {
	some u,u':User { some r,r':Repo{ some d:Data { some c:Secrets {
	CreatingRepo[u,r,s,s'] or DeletingRepo[u,r,s,s'] or GrantingRead[u,u',r,r',s,s']
	or RevokingRead[u,u',r,r',s,s'] or GrantingWrite[u,u',r,r',s,s'] or RevokingWrite[u,u',r,r',s,s']
	or Pushing[u,r,r',d,s,s'] or Pulling[u,u',r,d,s,s']
	or CreatingAccount [u,u',c,s,s'] or DeletingAccount[u,u',c,s,s']}}}}}

//Facts
fact ExistingReposWereCreated {
	all r:Repo { some u:User { some s,s':State { CreatingRepo[u,r,s,s'] }}}}
fact AllReposHaveOwners {
	all r:Repo { some u:User { u.name=r.owner }}}
fact Creation_Implies_Ownership {
	all u:User {all r:Repo {all s,s':State {
	CreatingRepo[u,r,s,s'] implies r.owner=u.name}}}}
fact Only_Owners_Delete_Repos {
	all u:User {all r:Repo {all s,s':State {
	DeletingRepo[u,r,s,s'] implies r.owner=u.name}}}}
fact OwnersCanWrite {
	all u:User { all r:Repo {
	r.owner=u.name implies u.name in r.writeUsers}}}
fact Repos_Can't_Share_Names {
	all r,r':Repo { all s:State {
	(r in s.repos && r' in s.repos && r != r') implies r.name != r'.name}}}
fact Only_Owners_Grant_and_Revoke_Access {
	all u,u':User { all r,r': Repo { all s,s':State {
	GrantingWrite[u,u',r,r',s,s'] or RevokingWrite[u,u',r,r',s,s'] or
	GrantingRead[u,u',r,r',s,s'] or RevokingRead[u,u',r,r',s,s'] implies u.name=r.owner && 
	u.name=r'.owner}}}}
fact All_Repos_and_Users_Have_States {
	all u:User { all r:Repo {some s:State { u in s.users && r in s.repos}}}}
fact Indistinguishable_States_Are_Identical {
	all s,s':State {s.users=s'.users && s.repos=s'.repos implies s=s'}}
fact Indistinguishable_Repos_Are_Identical {
	all r,r':Repo {r.name=r'.name && r.owner=r'.owner && r.readUsers=r'.readUsers &&
	r.writeUsers=r'.readUsers && r.contents=r'.contents implies r=r'}}
fact Indistinguishable_Users_Are_Identical {
	all u,u':User {u.name=u'.name && u.info=u'.info && u.action=u'.action
	&& u.secret=u'.secret implies u=u'}}
fact EachTransitionHasAUniqueStep {
	all s,s':State { Transition[s,s'] implies one u:User { one a:Actions {
	u in s.users && u.action=a && all u':User {u'.action != none implies u=u'}}}}}
fact OnlyCreatingAccountAcquiresSecrets {
	all u,u':User { all s,s':State { all c:Secrets { u in s.users && u' in s'.users && u.name=u'.name &&
	u.secret=none && u'.secret=c implies CreatingAccount[u,u',c,s,s'] }}}}
fact OnlyDeletingAccountGetsRidOfSecrets {
	all u,u':User { all s,s':State { all c:Secrets { u in s.users && u' in s'.users && u.name=u'.name &&
	u.secret=c && u'.secret=none implies DeletingAccount[u,u',c,s,s'] }}}}
fact OnlyOneSecretPerUser {
	all u:User {all c,c':Secrets { u.secret=c && u.secret=c' implies c=c' }}}
fact OnlyOneUserPerSecret {
	all u,u':User {all c:Secrets { u.secret=c && u'.secret=c implies u=u'}}}
fact AccountIsNecessaryforWriteAccess {
	all u:User { all r:Repo { u.name in r.writeUsers implies u.secret != none }}}

//Assertions
assert OwnersCannotRevokeTheirOwnAccess {
	all u,u':User { all r,r':Repo { all s,s':State {
	RevokingRead[u,u',r,r', s,s'] or RevokingWrite[u,u',r,r', s,s'] implies u != u'}}}}
assert NobodyCanCreateSomeoneElse'sAccount {
	all u,u',u'':User { all s,s':State { all c:Secrets { u.secret=c && u.name != u'.name implies
	not CreatingAccount[u',u'',c,s,s'] }}}}
assert NobodyCanDeleteSomeoneElse'sAccount {
	all u,u',u'':User { all s,s':State { all c:Secrets { u.secret=c && u.name != u'.name implies
	not DeletingAccount[u',u'',c,s,s'] }}}}
assert EveryOwnerHasAnAccount {
	all r:Repo { all u:User { u.name = r.owner implies u.secret != none }}}
assert WriteImpliesRead {
	all r:Repo { all u:User { u.name in r.writeUsers implies u.name in r.readUsers }}}
assert Grant_And_Revoke_Read_Are_Inverse {
	all u,u':User { all r,r',r'':Repo { all s,s',s'':State {
	(GrantingRead[u,u',r,r',s,s'] && RevokingRead[u,u',r',r'',s',s''] implies r=r'')
	&& (RevokingRead[u,u',r,r',s,s'] && GrantingRead[u,u',r',r'',s',s''] implies r=r'') }}}}
assert Grant_And_Revoke_Write_Are_Inverse {
	all u,u':User { all r,r',r'':Repo { all s,s',s'':State {
	(GrantingWrite[u,u',r,r',s,s'] && RevokingWrite[u,u',r',r'',s',s''] implies r=r'')
	&& (RevokingWrite[u,u',r,r',s,s'] && GrantingWrite[u,u',r',r'',s',s''] implies r=r'') }}}}
