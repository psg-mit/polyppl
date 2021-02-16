DataPoints Mu

acc645__l[k, mu] += obs[i]  # { [k, mu, i] : 0 <= k < DataPoints & 0 <= mu < Mu & 0 <= i < k } & z_new[i] == mu;
acc645__r[k, mu] += obs[i]  # { [k, mu, i] : 0 <= k < DataPoints & 0 <= mu < Mu & k < i < DataPoints } & z_old[i] == mu;
acc645_[k, mu] = acc645__l[k, mu] + acc645__r[k, mu] # { [k, mu] : 0 <= k < DataPoints & 0 <= mu < Mu };

acc646__l[k, mu] += 1  # { [k, mu, i] : 0 <= k < DataPoints & 0 <= mu < Mu & 0 <= i < k } & z_new[i] == mu;
acc646__r[k, mu] += 1  # { [k, mu, i] : 0 <= k < DataPoints & 0 <= mu < Mu & k < i < DataPoints } & z_old[i] == mu;
acc646_[k, mu] = acc646__l[k, mu] + acc646__r[k, mu] # { [k, mu] : 0 <= k < DataPoints & 0 <= mu < Mu };

