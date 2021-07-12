library(here)
require(ggplot2)
library(ggplot2)
#library(gganimate)
#library(gifski)
#library(av)

data <- read.csv(header=TRUE, sep = "#", 
                 file = here("/home/markus/src/TLA/_specs/models/tutorials/BlockingQueueTLA/BQPA_468267172.csv"))
## If prop is positive, the system is over-provisioned.
data <- within(data, prop <- ac - ap)

ggplot(data = data, aes(x = level, y = prop, color = factor(trace))) +
  # print discrete values
  geom_step() +
  # null line
  geom_hline(yintercept = 0, alpha = 0.3) +
  # more homogeneous colors.
  scale_color_viridis_d() +
  labs(x = "Length behavior (discrete time)", y = "Over- and under-provisioning (positive |ac|>|ap|") +
  theme(legend.position = "none")

########################

library(dplyr)
df <- data %>% group_by(trace,P,C,B) %>% summarise(over = max(prop), under = min(prop))
df <- df[c("P","C","B","over", "under")]
df <- df %>% group_by(P,C,B) %>% summarise(over = mean(over), under = mean(under))
df$Config <- paste(sep = ",", df$P, df$B)

########################

ggplot(df, aes(x = Config, y = over, fill = Config)) +
  geom_bar(stat = "identity") +
  #  scale_x_discrete(guide = guide_axis(n.dodge=3))+
  scale_x_discrete(guide = guide_axis(check.overlap = TRUE))+
  coord_flip() +
  theme_minimal() +
  theme(legend.position = "none") +
  labs(
    x = "Configuration",
    y = "Over- and under-provisioning (positive |ac|>|ap|)",
    title = paste(
      "Traces:", nrow(data)
    )
  )

ggplot(df) +
  geom_bar(aes(x=Config, y = over, fill=Config), stat="identity",position="dodge") + 
  geom_bar(aes(x=Config, y = under,fill=Config), stat="identity",position="dodge") +
#  scale_x_discrete(guide = guide_axis(n.dodge=3))+
  scale_x_discrete(guide = guide_axis(check.overlap = TRUE))+
  coord_flip() +
  theme_minimal() +
  theme(legend.position = "none") +
  labs(
    x = "Configuration",
    y = "Under- and over-provisioning of consumers (positive |ac|>|ap|)",
    title = paste(
      "Traces:", nrow(data)
    )
  )

########################

library("ggcorrplot")
p.mat <- cor_pmat(df)

## Check for correlation in 'data'
## 'spearman' (3) correlation because data has no normal distribution
## (see previous plots).
corr <- round(cor(df), 3)

ggcorrplot(corr, p.mat = cor_pmat(df),
           hc.order = TRUE, type = "lower",
           color = c("#FC4E07", "white", "#00AFBB"),
           outline.col = "white", lab = TRUE)

########################

# Plot ap and ac over time (level) as step functions.
ggplot(data = data, aes(x = level), color = factor(trace)) +
  geom_step(aes(y=ap), colour="red") +
  geom_step(aes(y=ac), colour="green")
