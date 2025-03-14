# Use ayberkt/agda-new:v2.3 as the base image
FROM ayberkt/agda-new:v2.3

# Install required packages for git and development
USER root
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
    git \
    make \
    # emacs-nox \
    # vim \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# # Determine which user exists in the base image
# # If the base image has a non-root user, use that
# # Otherwise, create a new user
# RUN if id -u agda >/dev/null 2>&1; then \
#       echo "Using existing agda user"; \
#       USER_NAME=agda; \
#     elif id -u proof >/dev/null 2>&1; then \
#       echo "Using existing proof user"; \
#       USER_NAME=proof; \
#     else \
#       echo "Creating new user 'researcher'"; \
#       useradd -ms /bin/bash researcher; \
#       USER_NAME=researcher; \
#     fi \
#     && echo "export USER_NAME=$USER_NAME" >> /etc/environment

# Get the user from environment
# ENV USER_NAME=${USER_NAME:-researcher}
# WORKDIR /home/$USER_NAME

# # Switch to the user
# USER $USER_NAME
#
ENV HOME=/home/$USER_NAME
ENV AGDA_DIR=$HOME/.agda
ENV AGDA_LIBS=$AGDA_DIR/libraries

# Set up Agda configuration directories
RUN mkdir -p AGDA_DR && touch AGDA_LIBS

# Install Cubical Agda library
WORKDIR $HOME
RUN git clone https://github.com/agda/cubical --branch master
WORKDIR $HOME/cubical
RUN git checkout 581748b01bc43a25295993347bdc8c7cb2166090
RUN echo "$HOME/cubical.agda-lib" >> $AGDA_LIBS

# Install Cubical Categorical Logic
WORKDIR $HOME
RUN git clone https://github.com/maxsnew/cubical-categorical-logic --branch main
WORKDIR $HOME/cubical-categorical-logic
RUN git checkout 4e7b1c3a2ba7ed528b3cd9a4c3a5e7be3ff3449d
RUN echo "$HOME/cubical-categorical-loigc.agda-lib" >> $AGDA_LIBS

COPY . $HOME/grammars-and-semantic-actions

WORKDIR /home/$USER_NAME/grammars-and-semantic-actions

# Default command
CMD ["/bin/bash"]
