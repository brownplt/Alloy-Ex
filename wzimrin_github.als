sig State {
	sUsers: set User,
	repos: set Repo,
	nextStates: set Action
}

fact {
	all s,s':State {
		transistion[s,s'] iff (some a:Action {
			a.state=s'
			transistionA[s,a]
		})
	}
	all s:State, a:Action {
		(a in s.nextStates) iff transistionA[s,a]
	}
	all s,s':State {
		(s.sUsers=s'.sUsers and s.repos= s'.repos) iff s=s'
		s' in s.*(nextStates.state) or s in s'.*(nextStates.state)
	}
}

sig User {
	name: one uName,
	dataKnown: set Data,
	dataMade: set Data,
}

fact {
	//can't have two users in the same state with the same name
	all u,u':User, s:State {
		(u in s.sUsers and u' in s.sUsers and u.name=u'.name) implies u=u'
	}
	//every user must be in a state
	all u:User {
		some s:State {
			u in s.sUsers
		}
	}
	//users are defined by their contents (will be expanded as users get more info)
	all u,u':User {
		(u.name=u'.name and
		u.dataKnown = u'.dataKnown and
		u.dataMade = u'.dataMade) implies u=u'
	}
	//users know all data they make
	all u:User, d:Data {
		d in u.dataMade implies d in u.dataKnown
	}
	//only one user can make a piece of data
	all u,u':User, d:Data {
		d in u.dataMade and d in u'.dataMade implies u.name=u'.name
	}
	all d:Data {
		some u:User {
			d in u.dataMade
		}
	}
}

sig Data {}

sig rName {}
sig uName {}

sig Repo {
	name: one rName,
	owner: one uName,
	users: set uName,
	contents: one Data,
} 

fact {
	//can't have two repos in the same state with the same name
	all r,r':Repo, s:State {
		(r in s.repos and r' in s.repos and r.name=r'.name) implies r=r'
	}
	//the owner is a user
	all r:Repo, u:uName {
		(r.owner = u) implies (u in r.users)
	}
	//the users must be in the same state
	all r:Repo, un:uName, s:State {
		(un in r.users) implies {
			(r in s.repos) implies (some u:User {u in s.sUsers and u.name=un})
		}
	}
	//repos are in at least one state
	all r:Repo {
		some s:State {
			r in s.repos
		}
	}
	//repos are uniquely defined by their fields
	all r,r':Repo {
		(r.name=r'.name and r.owner = r'.owner and r.users=r'.users and r.contents=r'.contents)
		implies r=r'
	}
}

abstract sig Action {
	state: one State
}

sig NoOp,CreateRepo,DeleteRepo,GrantAccess,RemoveAccess,
		MakeData,Push,Pull extends Action {}

fact {
	all a,a':NoOp {
		a.state=a'.state implies a=a'
	}
	all a,a':CreateRepo {
		a.state=a'.state implies a=a'
	}
	all a,a':DeleteRepo {
		a.state=a'.state implies a=a'
	}
	all a,a':GrantAccess {
		a.state=a'.state implies a=a'
	}
	all a,a':RemoveAccess {
		a.state=a'.state implies a=a'
	}
	all a,a':MakeData {
		a.state=a'.state implies a=a'
	}
	all a,a':Push {
		a.state=a'.state implies a=a'
	}
	all a,a':Pull {
		a.state=a'.state implies a=a'
	}
	all a:Action {
		some s:State {
			a in s.nextStates
		}
	}
}

pred transistion(s,s':State) {
	noop[s,s'] or
	(some u:User {
		createRepo[s,s',u] or
		deleteRepo[s,s',u]
	}) or
	(some o,u:User, r,r':Repo {
		grantAccess[s,s',o,u,r,r'] or
		removeAccess[s,s',o,u,r,r']
	}) or 
	(some u,u':User,d:Data {
		makeData[s,s',u,u',d]
	}) or
	(some u,u':User,r:Repo {
		pull[s,s',u,u',r]
	}) or
	(some u:User,r,r':Repo,d:Data {
		push[s,s',u,r,r',d]
	})
}

pred transistionA(s:State,a:Action) {
	(a in NoOp and noop[s,a.state]) or
	(some u:User {
		(a in CreateRepo and createRepo[s,a.state,u]) or
		(a in DeleteRepo and deleteRepo[s,a.state,u])
	}) or
	(some o,u:User, r,r':Repo {
		(a in GrantAccess and grantAccess[s,a.state,o,u,r,r']) or
		(a in RemoveAccess and removeAccess[s,a.state,o,u,r,r'])
	}) or 
	(some u,u':User,d:Data {
		a in MakeData and makeData[s,a.state,u,u',d]
	}) or
	(some u,u':User,r:Repo {
		a in Pull and pull[s,a.state,u,u',r]
	}) or
	(some u:User,r,r':Repo,d:Data {
		a in Push and push[s,a.state,u,r,r',d]
	})
}

pred onlyUsersChanged(s,s':State,us:set User) {
	all u:User {
		(u in s.sUsers) implies ((some u':User {
			u' in s'.sUsers
			u'.name = u.name
		}) or u in us)
		(u in s'.sUsers) implies ((some u':User {
			u' in s.sUsers
			u'.name = u.name
		}) or u in us)
	}
	all u,u':User {
		((u in s.sUsers) and (u' in s'.sUsers) and (u.name=u'.name)) implies {
			u=u' or (u in us and u' in us)
		}
	}
}

pred onlyRepoChanged(s,s':State,rs:set Repo) {
	all r:Repo {
		(r in s.repos) implies ((some r':Repo {
			r' in s'.repos
			r'.name = r.name
		}) or r in rs)
		(r in s'.repos) implies ((some r':Repo {
			r' in s.repos
			r'.name = r.name
		}) or r in rs)
	}
	all r,r':Repo {
		(r in s.repos and
		r' in s'.repos and
		r.name = r'.name) implies {
			r=r' or (r in rs and r' in rs)
		}
	}
}

pred noop(s,s':State) {s=s'}

pred createRepo(s,s':State, u:User) {
	onlyUsersChanged[s,s',none]
	u in s.sUsers
	some r:Repo {
		onlyRepoChanged[s,s',r]
		r in s'.repos
		!(r in s.repos)
		r.owner=u.name
		r.users=r.owner
		s.repos+r=s'.repos
	}
}

pred deleteRepo(s,s':State, u:User) {
	onlyUsersChanged[s,s',none]
	u in s.sUsers
	some r:Repo {
		onlyRepoChanged[s,s',r]
		r in s.repos
		!(r in s'.repos)
		r.owner = u.name
		s'.repos+r=s.repos
	}
}

pred grantAccess(s,s':State, o,u:User, r,r':Repo) {
	onlyUsersChanged[s,s',none]
	onlyRepoChanged[s,s',r+r']
	o in s.sUsers
	u in s.sUsers
	r in s.repos
	r.owner = o.name
	r' in s'.repos
	r.name = r'.name
	r.contents = r'.contents
	r.owner = r'.owner
	!(u.name in r.users)
	r.users + u.name = r'.users
}

pred removeAccess(s,s':State, o,u:User, r,r':Repo) {
	onlyUsersChanged[s,s',none]
	onlyRepoChanged[s,s',r+r']
	o in s.sUsers
	u in s.sUsers
	r in s.repos
	r.owner = o.name
	r' in s'.repos
	r.name = r'.name
	r.contents = r'.contents
	r.owner = r'.owner
	u.name in r.users
	r.users - u.name = r'.users
}

pred makeData(s,s':State,u,u':User,d:Data) {
	onlyUsersChanged[s,s',u+u']
	onlyRepoChanged[s,s',none]
	u in s.sUsers
	u' in s'.sUsers
	u.name=u'.name
	!(d in u.dataKnown)
	d in u'.dataMade
	u.dataMade+d = u'.dataMade
	u.dataKnown+d=u'.dataKnown
}

pred pull(s,s':State,u,u':User,r:Repo) {
	onlyUsersChanged[s,s',u+u']
	onlyRepoChanged[s,s',none]
	u in s.sUsers
	u' in s'.sUsers
	r in s.repos
	u.name = u'.name
	u.dataKnown = u'.dataKnown
	u.dataMade+r.contents = u'.dataMade
	u.name in r.users
}

pred push(s,s':State,u:User,r,r':Repo,d:Data) {
	onlyUsersChanged[s,s',none]
	onlyRepoChanged[s,s',r+r']
	u in s.sUsers
	r in s.repos
	r' in s'.repos
	r.users=r'.users
	r.owner = r'.owner
	r.name = r'.name
	r'.contents = d
	d in u.dataKnown
	u.name in r.users
}

pred example {some s,s':State{s.repos != none and s != s'}}
pred combo {
	some s,s':State, u:User {
		createRepo[s,s',u]
	}
	some s,s':State, o,u:User, r,r':Repo {
		grantAccess[s,s',o,u,r,r']
	}
	some s,s':State, u,u':User, r:Repo {
		pull[s,s',u,u',r]
	}
	some s,s':State, u:User, r,r':Repo, d:Data {
		push[s,s',u,r,r',d]
	}
	some s,s':State, u,u':User, d:Data {
		makeData[s,s',u,u',d]
	}
}

assert grantRemoveAccessInverses {
	all s,s':State,o,u:User,r,r':Repo {
		grantAccess[s,s',o,u,r,r'] iff
		removeAccess[s',s,o,u,r',r]
	}
}

assert learningDataRequiresReadAccess {
	//
}

run combo for 5 but 10 Action
//check grantRemoveAccessInverses for 6
