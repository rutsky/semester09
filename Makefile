# Makefile
# Some common tasks for whole project.
# Vladimir Rutsky <altsysrq@gmail.com>
# 20.05.2009

GIT_PATH_GITHUB=git@github.com:rutsky/semester09.git
GIT_PATH_GITORIOUS=git@gitorious.org:spbstu/semester09.git

all:
	@echo "Read Makefile contents for details of usage."

git-init:
	git remote add github    $(GIT_PATH_GITHUB)
	git remote add gitorious $(GIT_PATH_GITORIOUS)

public:
	git push github    master
	git push gitorious master

update:
	git fetch github
	git merge github/master

clean-light:
	find . -name '*.o' -exec rm '{}' \;
	find . -wholename '*.gch/c++' -exec rm '{}' \;

archive:
	tar -cf ../semester09_`date +%F_%H-%M-%S`.tar ./
