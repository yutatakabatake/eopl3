FROM arm64v8/fedora:40

ARG INSTALL_SCRPT_URL=https://raw.githubusercontent.com/microsoft/vscode-dev-containers/main/script-library/common-redhat.sh

RUN curl -O $INSTALL_SCRPT_URL && \ 
   chmod +x common-redhat.sh && \ 
   ./common-redhat.sh&& \
   rm common-redhat.sh

RUN yum install -y \
   racket.aarch64 \
   xorg-x11-server-Xvfb.aarch64
RUN yum clean all

RUN raco setup
RUN raco pkg install --auto -i racket-langserver eopl

USER vscode

CMD ["bash"]